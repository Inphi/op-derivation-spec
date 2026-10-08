/-
  OP Stack derivation: single-batch validity (Layer 1 spec)

  Source of truth, in order of precedence:
    * specs.optimism.io/protocol/derivation.html, section "Batch Queue",
      list "Rules, in validation order"
    * fork deltas folded in: Holocene (`future` becomes `drop`, new `past` verdict),
      Isthmus (SetCode txs), Lagoon/SDM (PostExec txs), and the Jovian/Karst/Lagoon
      rule that fork-activation blocks carry no sequencer transactions.

  Design choices
    * Mathematical `Nat` everywhere. Rust's u64 wrap-around is deliberately NOT part of
      the spec; the refinement layer adds a `Bounded` precondition under which no u64
      operation in the implementation wraps.
    * The fork schedule is abstract (`Nat → Bool`), so every theorem in `Theorems.lean`
      holds for every fork schedule. The refinement layer instantiates these with
      kona-genesis's `is_*_active` predicates.
    * Hashes are only ever compared for equality, so `Hash := Nat` is enough; the
      refinement layer maps `FixedBytes<32>` injectively into it.
    * The rule is stated over `epoch` and `next_epoch?` exactly as the prose does
      (`batchValidityCore`). `batchValidity` is a thin wrapper over the `l1_blocks`
      slice that kona and op-node actually pass around.
-/
namespace OpDerivation

abbrev Hash := Nat

structure BlockId where
  num  : Nat
  hash : Hash
  deriving DecidableEq, Repr

/-- An L1 block reference (kona `BlockInfo`, minus fields this rule never reads). -/
structure L1Ref where
  num  : Nat
  hash : Hash
  time : Nat
  deriving DecidableEq, Repr

def L1Ref.id (b : L1Ref) : BlockId := ⟨b.num, b.hash⟩

/-- The current safe L2 head (kona `L2BlockInfo`). -/
structure L2Ref where
  hash   : Hash
  time   : Nat
  origin : BlockId
  deriving DecidableEq, Repr

/-- A singular sequencer batch (kona `SingleBatch`).
    Transactions are opaque EIP-2718 byte strings; only the first byte is inspected. -/
structure SingleBatch where
  parentHash : Hash
  epochNum   : Nat
  epochHash  : Hash
  time       : Nat
  txs        : List (List UInt8)
  deriving DecidableEq, Repr

/-- The slice of `RollupConfig` this rule depends on. -/
structure Cfg where
  /-- `l2_block_time` -/
  blockTime     : Nat
  /-- `seq_window_size`, in L1 blocks -/
  seqWindowSize : Nat
  /-- `max_sequencer_drift`, as a function of the L1 origin time (a constant 1800 after Fjord). -/
  maxDrift      : Nat → Nat
  /-- Holocene active, evaluated at the L1 *inclusion block* time. -/
  holocene      : Nat → Bool
  /-- Isthmus active, evaluated at the L2 batch time. -/
  isthmus       : Nat → Bool
  /-- Sequencer-Defined Metering (Lagoon) active, evaluated at the L2 batch time. -/
  sdm           : Nat → Bool
  /-- The L2 block at this time is a fork activation block that must carry no sequencer
      transactions (Jovian, Karst, Lagoon/Interop). See note (3) in the README on how
      op-node and kona define "activation block". -/
  emptyRequired : Nat → Bool

inductive Validity
  | accept | drop | future | undecided | past
  deriving DecidableEq, Repr

/-! ## Sequencer transaction policy -/

def DEPOSIT_TX_TYPE  : UInt8 := 0x7E
def SETCODE_TX_TYPE  : UInt8 := 0x04
def POSTEXEC_TX_TYPE : UInt8 := 0x7D

/-- Per-transaction rule as implemented by BOTH op-node (`checkSequencerTxData`) and kona
    (`SingleBatch::check_batch`): only empty txs, deposits, and not-yet-activated types are
    rejected. Any other leading byte, including type 0x03 and unassigned types, is accepted
    here and left to the execution engine.

    SPEC GAP: the prose additionally drops "any transaction of a future type > 2".
    See `txAllowedProse` and `Theorems.spec_gap_type3`. This file follows the
    implementations, because that is what consensus runs today; flip `batchValidityCore`
    to `txAllowedProse` if the prose is the intended rule. -/
def txAllowed (c : Cfg) (t : Nat) : List UInt8 → Bool
  | [] => false
  | ty :: _ =>
    if ty = DEPOSIT_TX_TYPE then false
    else if ty = SETCODE_TX_TYPE then c.isthmus t
    else if ty = POSTEXEC_TX_TYPE then c.sdm t
    else true

/-- A literal reading of the prose rule. Legacy txs are recognised by an RLP list header
    (first byte in [0xc0, 0xfe], per "On Future-Proof Transaction Log Derivation").
    Anything that is neither a known typed tx nor legacy is treated as invalid. -/
def txAllowedProse (c : Cfg) (t : Nat) : List UInt8 → Bool
  | [] => false
  | ty :: _ =>
    if ty = DEPOSIT_TX_TYPE then false
    else if ty = SETCODE_TX_TYPE then c.isthmus t
    else if ty = POSTEXEC_TX_TYPE then c.sdm t
    else if ty ≤ 0x02 then true
    else if 0xC0 ≤ ty ∧ ty ≤ 0xFE then true
    else false

/-- The checks that run after all timing/origin rules have passed. -/
def txChecks (c : Cfg) (b : SingleBatch) : Validity :=
  if c.emptyRequired b.time = true ∧ b.txs ≠ [] then .drop
  else if b.txs.all (txAllowed c b.time) then .accept
  else .drop

/-! ## The rule -/

/-- Batch validity, stated over the prose's own inputs:
    `epoch` is the safe head's L1 origin, and `next?` is the next L1 block if it is
    already known ("`next_epoch` may not be known yet"). Each branch is one bullet of
    "Rules, in validation order". -/
def batchValidityCore (c : Cfg) (epoch : L1Ref) (next? : Option L1Ref)
    (safe : L2Ref) (incl : L1Ref) (b : SingleBatch) : Validity :=
  let nextTime := safe.time + c.blockTime
  -- batch.timestamp > next_timestamp  →  future (pre-Holocene) / drop (Holocene)
  if nextTime < b.time then
    if c.holocene incl.time then .drop else .future
  -- batch.timestamp < next_timestamp  →  drop (pre-Holocene) / past (Holocene)
  else if b.time < nextTime then
    if c.holocene incl.time then .past else .drop
  -- batch.parent_hash != safe_l2_head.hash  →  drop
  else if b.parentHash ≠ safe.hash then .drop
  -- batch.epoch_num + sequence_window_size < inclusion_block_number  →  drop
  else if b.epochNum + c.seqWindowSize < incl.num then .drop
  -- batch.epoch_num < epoch.number  →  drop
  else if b.epochNum < epoch.num then .drop
  -- batch.epoch_num > epoch.number + 1  →  drop
  else if epoch.num + 1 < b.epochNum then .drop
  else
    -- batch_origin := epoch, or next_epoch (undecided if not yet known)
    match (if b.epochNum = epoch.num then some epoch else next?) with
    | none => .undecided
    | some origin =>
      -- batch.epoch_hash != batch_origin.hash  →  drop
      if b.epochHash ≠ origin.hash then .drop
      -- batch.timestamp < batch_origin.time  →  drop
      else if b.time < origin.time then .drop
      -- batch.timestamp > batch_origin.time + max_sequencer_drift  →  …
      else if origin.time + c.maxDrift origin.time < b.time then
        -- …with transactions  →  drop
        if b.txs ≠ [] then .drop
        -- …empty, not advancing the origin: valid only if next origin could not be adopted
        else if b.epochNum = epoch.num then
          match next? with
          | none => .undecided
          | some next => if next.time ≤ b.time then .drop else txChecks c b
        else txChecks c b
      else txChecks c b

/-- The same rule over the `l1_blocks` slice used by kona and op-node:
    `l1_blocks[0]` is the epoch and `l1_blocks[1]`, if present, the next epoch. -/
def batchValidity (c : Cfg) (l1 : List L1Ref) (safe : L2Ref) (incl : L1Ref)
    (b : SingleBatch) : Validity :=
  match l1 with
  | [] => .undecided
  | epoch :: rest => batchValidityCore c epoch rest.head? safe incl b

end OpDerivation
