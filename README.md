# OP derivation spec: single-batch validity

A Lean 4 formalization of the OP Stack batch-validity rule ("Batch Queue → Rules, in
validation order" in the derivation spec), plus machine-checked properties of it, set up
so that kona's `SingleBatch::check_batch` can later be proven to refine it via Aeneas.

The project targets Lean `v4.31.0`, the same toolchain Aeneas pins, and uses only core
Lean (no Mathlib). Everything under `DerivationSpec/` builds with no `sorry`; the
theorems depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

```
lake build
```

## Layout

`DerivationSpec/BatchValidity.lean` is the Layer 1 spec. `batchValidityCore` is
stated over the prose's own inputs (`epoch`, and `next_epoch` if known), one branch per
bullet. `batchValidity` wraps it over the `l1_blocks` slice that kona and op-node pass
around. Fork activation is abstract (`Nat → Bool`), so every theorem holds for every
fork schedule.

`DerivationSpec/Theorems.lean` holds the Layer 2 properties, all proven:

| Theorem | Statement |
|---|---|
| `accept_sound` | An accepted batch satisfies every rule: parent hash, exact timestamp, inclusion window, origin is the epoch or the next L1 block with matching hash, L2 time ≥ L1 origin time, drift rule, activation-block rule, per-tx rule. |
| `accept_overview` | The spec's Overview constraints, given that `l1_blocks[0]` is the safe head's origin: one block per `l2_block_time`; origin advances by 0 or 1; `l1_origin.time ≤ block.time`; past the drift bound, no sequencer txs. |
| `accept_no_deposits` | No accepted batch contains an empty transaction or a deposit (type 0x7E). |
| `undecided_needs_more_l1` | `undecided` only happens with fewer than two L1 blocks. |
| `eager_stable` | Appending L1 blocks never changes a decided verdict. This is the correctness condition for eager block derivation that op-node and kona both warn about in comments. |
| `spec_gap_type3` | Witness for discrepancy 1 below. |

`DerivationSpec/Examples.lean` has 16 test vectors evaluated by the kernel at build
time (happy path, epoch advance, Holocene future/past, window expiry, the drift cases,
tx rules). They are meant to be replayed against op-node and kona for differential
testing before any refinement proof exists.

`refinement/CheckBatchRefinement.lean` is a template, not built: abstraction functions
from Aeneas-extracted kona types to spec types, the `Bounded` and `Contiguous`
preconditions, and the statement of `check_batch_refines`.
