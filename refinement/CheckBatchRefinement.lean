/-
  TEMPLATE: not part of the Lake build, and not type-checked.

  This file connects the Layer 1 spec (`DerivationSpec.BatchValidity`) to kona's
  `SingleBatch::check_batch` once Aeneas has extracted `kona-protocol`. Generated
  identifiers below follow Aeneas's convention of mirroring Rust paths, but they are
  guesses: regenerate, then fix names and field accessors to match `Types.lean`.

  Prerequisites (README, "Getting check_batch through Aeneas"):
    1. `charon cargo --preset=aeneas` inside kona-protocol, with `tracing` compiled out
    2. `aeneas -backend lean -split-files kona_protocol.llbc`
    3. hand-written models in `FunsExternal.lean` for alloy `Bytes` (as a list of
       bytes), `OpTxType::try_from`, and the `RollupConfig` fork predicates
       (or extract kona-genesis as well)

  Proof style follows the Aeneas tutorial: `f args ⦃ r => post ⦄` triples, discharged
  with `step*` and `scalar_tac`.
-/
import Aeneas
import KonaProtocol.Funs   -- generated
import DerivationSpec

open Aeneas Std Result
open OpDerivation

namespace OpDerivation.Refinement

abbrev RBatch    := kona_protocol.batch.single.SingleBatch
abbrev RBlock    := kona_protocol.block.BlockInfo
abbrev RL2Block  := kona_protocol.block.L2BlockInfo
abbrev RConfig   := kona_genesis.rollup.RollupConfig
abbrev RValidity := kona_protocol.batch.validity.BatchValidity

-- Helper models still to write (pure Lean, next to FunsExternal.lean):
--   bytesModel             : alloy_primitives.bytes_.Bytes → List U8
--   forkActive             : Option U64 → Nat → Bool
--   maxSequencerDriftModel : RConfig → Nat → Nat
--   firstJovian, firstKarst, firstLagoon : RConfig → Nat → Bool

/-! ## Abstraction functions: Rust values → spec values -/

/-- Big-endian value of the 32 bytes. Injective, which is all the refinement needs,
    since the spec only compares hashes for equality. -/
def absHash (h : alloy_primitives.bits.fixed.FixedBytes) : Hash :=
  h.val.val.foldl (fun acc x => acc * 256 + x.val) 0

def absL1 (b : RBlock) : L1Ref :=
  ⟨b.number.val, absHash b.hash, b.timestamp.val⟩

def absL2 (h : RL2Block) : L2Ref :=
  ⟨absHash h.block_info.hash, h.block_info.timestamp.val,
   ⟨h.l1_origin.number.val, absHash h.l1_origin.hash⟩⟩

/-- `bytesModel` is the hand-written model of alloy `Bytes` from FunsExternal. -/
def absBatch (b : RBatch) : SingleBatch :=
  ⟨absHash b.parent_hash, b.epoch_num.val, absHash b.epoch_hash, b.timestamp.val,
   b.transactions.val.map fun tx => (bytesModel tx).map fun x => UInt8.ofNat x.val⟩

/-- Pure versions of kona-genesis's predicates. Each needs a companion lemma, e.g.
      `RollupConfig.is_holocene_active cfg t ⦃ r => r = (absCfg cfg).holocene t.val ⦄`.
    Watch for fork implication (kona's `is_jovian_active` is also true when Karst is). -/
def absCfg (c : RConfig) : Cfg where
  blockTime     := c.block_time.val
  seqWindowSize := c.seq_window_size.val
  maxDrift      := fun t => maxSequencerDriftModel c t
  holocene      := fun t => forkActive c.hardforks.holocene_time t
  isthmus       := fun t => forkActive c.hardforks.isthmus_time t
  sdm           := fun t => forkActive c.hardforks.lagoon_time t
  -- kona: `is_first_{jovian,karst,lagoon}_block`, using `saturating_sub`.
  -- op-node additionally requires `t ≥ block_time`; the two agree on every batch that
  -- reaches this check, because there `t = safe.time + block_time` (README note 3).
  emptyRequired := fun t => firstJovian c t || firstKarst c t || firstLagoon c t

def absValidity : RValidity → Validity
  | .Accept    => .accept
  | .Drop _    => .drop        -- drop reasons are kona-specific; the spec does not name them
  | .Future    => .future
  | .Undecided => .undecided
  | .Past      => .past

/-! ## Preconditions the refinement needs

  Both are facts about the caller, not the rule. Proving them about `BatchQueue` is the
  next milestone. -/

/-- No u64 operation inside `check_batch` wraps. Production builds set
    `overflow-checks = false`, so a wrap would be silent; Aeneas instead models it as
    failure, which is why the triple below also proves panic- and wrap-freedom. -/
def Bounded (c : RConfig) (l1 : Slice RBlock) (safe : RL2Block) (b : RBatch) : Prop :=
  safe.block_info.timestamp.val + c.block_time.val ≤ U64.max ∧
  b.epoch_num.val + c.seq_window_size.val ≤ U64.max ∧
  (∀ o ∈ l1.val, o.number.val < U64.max) ∧
  -- kona uses `checked_add` here and drops on overflow; the spec has no such branch
  (∀ o ∈ l1.val.take 2, o.timestamp.val + maxSequencerDriftModel c o.timestamp.val ≤ U64.max)

/-- `l1_blocks[1]`, when present, is the block right after `l1_blocks[0]`.
    Needed because kona tests `epoch.number == batch_origin.number` where the spec tests
    `batch.epoch_num == epoch.number`; these agree only on contiguous input. -/
def Contiguous (l1 : Slice RBlock) : Prop :=
  ∀ e n rest, l1.val = e :: n :: rest → n.number.val = e.number.val + 1

/-! ## The refinement theorem -/

theorem check_batch_refines
    (b : RBatch) (cfg : RConfig) (l1 : Slice RBlock) (safe : RL2Block) (incl : RBlock)
    (hB : Bounded cfg l1 safe b) (hC : Contiguous l1) :
    kona_protocol.batch.single.SingleBatch.check_batch b cfg l1 safe incl ⦃ v =>
      absValidity v =
        batchValidity (absCfg cfg) (l1.val.map absL1) (absL2 safe) (absL1 incl) (absBatch b) ⦄ := by
  unfold kona_protocol.batch.single.SingleBatch.check_batch
  -- Expected shape: `step*` walks the extracted monadic code; each leaf is closed by
  -- `simp [batchValidity, batchValidityCore, txChecks, txAllowed]` plus `scalar_tac`
  -- for the arithmetic side conditions supplied by `hB`. The tx loop needs its own
  -- loop-spec lemma relating it to `List.all (txAllowed …)`.
  sorry

/-! ## Transfer: Layer 2 theorems now hold for kona

  With `check_batch_refines` in hand, each theorem in `DerivationSpec.Theorems`
  carries over by rewriting with `absValidity v = batchValidity …`. For example: -/

theorem kona_never_accepts_deposits
    (b : RBatch) (cfg : RConfig) (l1 : Slice RBlock) (safe : RL2Block) (incl : RBlock)
    (hB : Bounded cfg l1 safe b) (hC : Contiguous l1) :
    kona_protocol.batch.single.SingleBatch.check_batch b cfg l1 safe incl ⦃ v =>
      v = .Accept →
        ∀ tx ∈ (absBatch b).txs, ∃ ty rest, tx = ty :: rest ∧ ty ≠ DEPOSIT_TX_TYPE ⦄ := by
  -- weaken `check_batch_refines` with `accept_no_deposits`
  sorry

end OpDerivation.Refinement
