import DerivationSpec.BatchValidity

/-
  Test vectors. Each `example` is evaluated by the Lean kernel during `lake build`, so the
  spec doubles as an executable reference. The same scenarios can be replayed against
  op-node's `checkSingularBatch` and kona's `SingleBatch::check_batch` for differential
  testing before any refinement proof exists.

  Toy parameters: 2s L2 blocks, 10-block sequencing window, 30s drift,
  Holocene active for L1 inclusion times ≥ 1000, and the L2 block at t = 500 is a fork
  activation block.
-/
namespace OpDerivation.Examples
open OpDerivation

def cfg : Cfg where
  blockTime     := 2
  seqWindowSize := 10
  maxDrift      := fun _ => 30
  holocene      := fun t => decide (1000 ≤ t)
  isthmus       := fun _ => false
  sdm           := fun _ => false
  emptyRequired := fun t => decide (t = 500)

--                    num  hash    time
def e100 : L1Ref := ⟨100, 0xa100, 200⟩
def e101 : L1Ref := ⟨101, 0xa101, 212⟩
def e101late : L1Ref := ⟨101, 0xa101, 250⟩

/-- Safe head at t = 210 with L1 origin #100. -/
def safe : L2Ref := ⟨0xb0, 210, ⟨100, 0xa100⟩⟩
/-- Safe head at t = 240, already past origin #100's drift bound (200 + 30). -/
def safeLate : L2Ref := ⟨0xb0, 240, ⟨100, 0xa100⟩⟩

def incl      : L1Ref := ⟨103, 0xa103, 236⟩
def inclHolo  : L1Ref := ⟨103, 0xa103, 1236⟩
def inclLate  : L1Ref := ⟨111, 0xa111, 332⟩

def mk (epochNum : Nat) (epochHash : Hash) (time : Nat) (txs : List (List UInt8)) :
    SingleBatch := ⟨0xb0, epochNum, epochHash, time, txs⟩

def tx1559    : List UInt8 := [0x02, 0xf8, 0x6c]
def txLegacy  : List UInt8 := [0xf8, 0x6c]
def txDeposit : List UInt8 := [0x7e, 0xf8]
def txBlob    : List UInt8 := [0x03, 0xf8]

/-! Happy path -/
example : batchValidity cfg [e100] safe incl (mk 100 0xa100 212 [tx1559, txLegacy]) = .accept := by
  decide

/-! Advancing the L1 origin needs `next_epoch` -/
example : batchValidity cfg [e100] safe incl (mk 101 0xa101 212 [tx1559]) = .undecided := by
  decide
example : batchValidity cfg [e100, e101] safe incl (mk 101 0xa101 212 [tx1559]) = .accept := by
  decide
-- …and must reference the canonical next block
example : batchValidity cfg [e100, e101] safe incl (mk 101 0xdead 212 [tx1559]) = .drop := by
  decide

/-! Timestamp rules, before and after Holocene -/
example : batchValidity cfg [e100] safe incl     (mk 100 0xa100 214 []) = .future := by decide
example : batchValidity cfg [e100] safe inclHolo (mk 100 0xa100 214 []) = .drop   := by decide
example : batchValidity cfg [e100] safe incl     (mk 100 0xa100 210 []) = .drop   := by decide
example : batchValidity cfg [e100] safe inclHolo (mk 100 0xa100 210 []) = .past   := by decide

/-! Sequencing window -/
example : batchValidity cfg [e100] safe inclLate (mk 100 0xa100 212 [tx1559]) = .drop := by
  decide

/-! Sequencer drift: batch at t = 242 > 200 + 30 -/
-- with transactions: dropped
example : batchValidity cfg [e100, e101late] safeLate incl (mk 100 0xa100 242 [tx1559]) = .drop := by
  decide
-- empty, next origin not yet known: undecided
example : batchValidity cfg [e100] safeLate incl (mk 100 0xa100 242 []) = .undecided := by
  decide
-- empty, but the next origin (t = 212) could have been adopted: dropped
example : batchValidity cfg [e100, e101] safeLate incl (mk 100 0xa100 242 []) = .drop := by
  decide
-- empty, and the next origin (t = 250) is still in the future: accepted
example : batchValidity cfg [e100, e101late] safeLate incl (mk 100 0xa100 242 []) = .accept := by
  decide

/-! Transaction rules -/
example : batchValidity cfg [e100] safe incl (mk 100 0xa100 212 [tx1559, txDeposit]) = .drop := by
  decide
example : batchValidity cfg [e100] safe incl (mk 100 0xa100 212 [[]]) = .drop := by
  decide
-- Spec gap: a type-0x03 transaction is accepted, matching op-node and kona (see README)
example : batchValidity cfg [e100] safe incl (mk 100 0xa100 212 [txBlob]) = .accept := by
  decide

end OpDerivation.Examples
