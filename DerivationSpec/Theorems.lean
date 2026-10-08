import DerivationSpec.BatchValidity

/-
  Layer 2: properties of the spec itself.

  Nothing here mentions Rust. Once `check_batch` is shown to refine `batchValidity`
  (see `refinement/CheckBatchRefinement.lean`), every theorem below transfers to kona
  for free.

  All proofs use only core Lean 4 (no Mathlib), so this builds in seconds against the
  same toolchain Aeneas pins.
-/
namespace OpDerivation

/-! ## Helper lemmas about the trailing transaction checks -/

theorem txChecks_accept {c : Cfg} {b : SingleBatch} (h : txChecks c b = .accept) :
    (c.emptyRequired b.time = true → b.txs = []) ∧
    (∀ tx ∈ b.txs, txAllowed c b.time tx = true) := by
  unfold txChecks at h
  split at h
  · contradiction
  · split at h
    · rename_i h1 h2
      refine ⟨fun he => ?_, ?_⟩
      · exact Classical.byContradiction fun hne => h1 ⟨he, hne⟩
      · simpa [List.all_eq_true] using h2
    · contradiction

theorem txChecks_ne_undecided (c : Cfg) (b : SingleBatch) : txChecks c b ≠ .undecided := by
  unfold txChecks; split <;> (try split) <;> simp

/-! ## 1. Soundness: an accepted batch satisfies every rule it was checked against -/

theorem core_accept {c : Cfg} {epoch : L1Ref} {next? : Option L1Ref} {safe : L2Ref}
    {incl : L1Ref} {b : SingleBatch}
    (h : batchValidityCore c epoch next? safe incl b = .accept) :
    ∃ origin,
      (origin = epoch ∧ b.epochNum = epoch.num ∨
       next? = some origin ∧ b.epochNum = epoch.num + 1) ∧
      b.parentHash = safe.hash ∧
      b.time = safe.time + c.blockTime ∧
      incl.num ≤ b.epochNum + c.seqWindowSize ∧
      b.epochHash = origin.hash ∧
      origin.time ≤ b.time ∧
      (origin.time + c.maxDrift origin.time < b.time →
         b.txs = [] ∧
         (b.epochNum = epoch.num → ∃ next, next? = some next ∧ b.time < next.time)) ∧
      (c.emptyRequired b.time = true → b.txs = []) ∧
      (∀ tx ∈ b.txs, txAllowed c b.time tx = true) := by
  unfold batchValidityCore at h
  dsimp only at h
  by_cases h1 : safe.time + c.blockTime < b.time
  · rw [if_pos h1] at h; cases hh : c.holocene incl.time <;> simp [hh] at h
  rw [if_neg h1] at h
  by_cases h2 : b.time < safe.time + c.blockTime
  · rw [if_pos h2] at h; cases hh : c.holocene incl.time <;> simp [hh] at h
  rw [if_neg h2] at h
  by_cases h3 : b.parentHash ≠ safe.hash
  · rw [if_pos h3] at h; contradiction
  rw [if_neg h3] at h
  by_cases h4 : b.epochNum + c.seqWindowSize < incl.num
  · rw [if_pos h4] at h; contradiction
  rw [if_neg h4] at h
  by_cases h5 : b.epochNum < epoch.num
  · rw [if_pos h5] at h; contradiction
  rw [if_neg h5] at h
  by_cases h6 : epoch.num + 1 < b.epochNum
  · rw [if_pos h6] at h; contradiction
  rw [if_neg h6] at h
  have hTime : b.time = safe.time + c.blockTime := by omega
  have hPar : b.parentHash = safe.hash := Decidable.of_not_not h3
  have hIncl : incl.num ≤ b.epochNum + c.seqWindowSize := by omega
  generalize hO : (if b.epochNum = epoch.num then some epoch else next?) = o at h
  rcases o with _ | origin
  · contradiction
  dsimp only at h
  have hOrig : origin = epoch ∧ b.epochNum = epoch.num ∨
      next? = some origin ∧ b.epochNum = epoch.num + 1 := by
    by_cases he : b.epochNum = epoch.num
    · rw [if_pos he] at hO; exact Or.inl ⟨(Option.some.inj hO).symm, he⟩
    · rw [if_neg he] at hO; exact Or.inr ⟨hO, by omega⟩
  by_cases h7 : b.epochHash ≠ origin.hash
  · rw [if_pos h7] at h; contradiction
  rw [if_neg h7] at h
  have hHash : b.epochHash = origin.hash := Decidable.of_not_not h7
  by_cases h8 : b.time < origin.time
  · rw [if_pos h8] at h; contradiction
  rw [if_neg h8] at h
  have hLow : origin.time ≤ b.time := by omega
  by_cases h9 : origin.time + c.maxDrift origin.time < b.time
  · rw [if_pos h9] at h
    by_cases h10 : b.txs ≠ []
    · rw [if_pos h10] at h; contradiction
    rw [if_neg h10] at h
    have hEmpty : b.txs = [] := Decidable.of_not_not h10
    by_cases he : b.epochNum = epoch.num
    · rw [if_pos he] at h
      rcases hn : next? with _ | next
      · rw [hn] at h; contradiction
      · rw [hn] at h; dsimp only at h
        by_cases h11 : next.time ≤ b.time
        · rw [if_pos h11] at h; contradiction
        rw [if_neg h11] at h
        obtain ⟨hE, hT⟩ := txChecks_accept h
        exact ⟨origin, hn ▸ hOrig, hPar, hTime, hIncl, hHash, hLow,
          fun _ => ⟨hEmpty, fun _ => ⟨next, rfl, by omega⟩⟩, hE, hT⟩
    · rw [if_neg he] at h
      obtain ⟨hE, hT⟩ := txChecks_accept h
      exact ⟨origin, hOrig, hPar, hTime, hIncl, hHash, hLow,
        fun _ => ⟨hEmpty, fun he' => absurd he' he⟩, hE, hT⟩
  · rw [if_neg h9] at h
    obtain ⟨hE, hT⟩ := txChecks_accept h
    exact ⟨origin, hOrig, hPar, hTime, hIncl, hHash, hLow,
      fun hd => absurd hd h9, hE, hT⟩

/-- Soundness over the `l1_blocks` slice. -/
theorem accept_sound {c : Cfg} {l1 : List L1Ref} {safe : L2Ref} {incl : L1Ref}
    {b : SingleBatch} (h : batchValidity c l1 safe incl b = .accept) :
    ∃ epoch rest origin, l1 = epoch :: rest ∧
      (origin = epoch ∧ b.epochNum = epoch.num ∨
       rest.head? = some origin ∧ b.epochNum = epoch.num + 1) ∧
      b.parentHash = safe.hash ∧
      b.time = safe.time + c.blockTime ∧
      incl.num ≤ b.epochNum + c.seqWindowSize ∧
      b.epochHash = origin.hash ∧
      origin.time ≤ b.time ∧
      (origin.time + c.maxDrift origin.time < b.time →
         b.txs = [] ∧
         (b.epochNum = epoch.num → ∃ next, rest.head? = some next ∧ b.time < next.time)) ∧
      (c.emptyRequired b.time = true → b.txs = []) ∧
      (∀ tx ∈ b.txs, txAllowed c b.time tx = true) := by
  match l1, h with
  | [], h => simp [batchValidity] at h
  | epoch :: rest, h =>
    obtain ⟨origin, rest'⟩ := core_accept h
    exact ⟨epoch, rest, origin, rfl, rest'⟩

/-! ## 2. The Overview constraints

  The spec's Overview requires, for each L2 block with L1 origin `l1_origin`:
    * `block.timestamp = prev_l2_timestamp + l2_block_time`
    * `l1_origin.timestamp <= block.timestamp <= max_l2_timestamp`
  and the Batch Queue section adds that the origin advances by at most one L1 block and
  that no sequencer transactions are allowed past the drift bound.

  Note: with `max_l2_timestamp = max(l1_origin.timestamp + max_sequencer_drift,
  prev_l2_timestamp + l2_block_time)`, the upper bound follows from the first equation
  and carries no information. The real content of the drift rule is clause (4) below. -/

theorem accept_overview {c : Cfg} {l1 : List L1Ref} {safe : L2Ref} {incl : L1Ref}
    {b : SingleBatch}
    (hEpoch : l1.head?.map L1Ref.id = some safe.origin)
    (h : batchValidity c l1 safe incl b = .accept) :
    -- (1) one L2 block every `l2_block_time`
    b.time = safe.time + c.blockTime ∧
    -- (2) the L1 origin is the parent's origin or the one right after it
    (b.epochNum = safe.origin.num ∨ b.epochNum = safe.origin.num + 1) ∧
    ∃ origin, origin ∈ l1.take 2 ∧ origin.hash = b.epochHash ∧
      -- (3) L2 time never precedes L1 origin time
      origin.time ≤ b.time ∧
      -- (4) past the drift bound, no sequencer transactions
      (origin.time + c.maxDrift origin.time < b.time → b.txs = []) := by
  obtain ⟨epoch, rest, origin, rfl, hOrig, -, hTime, -, hHash, hLow, hDrift, -, -⟩ :=
    accept_sound h
  have hE : epoch.num = safe.origin.num := by
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hEpoch
    rw [← hEpoch]; rfl
  refine ⟨hTime, ?_, origin, ?_, hHash.symm, hLow, fun hd => (hDrift hd).1⟩
  · rcases hOrig with ⟨-, hn⟩ | ⟨-, hn⟩ <;> omega
  · rcases hOrig with ⟨rfl, -⟩ | ⟨hn, -⟩
    · simp
    · cases rest with
      | nil => simp at hn
      | cons n rest => simp at hn; simp [hn]

/-! ## 3. Sequencers cannot inject deposits or empty transactions -/

theorem accept_no_deposits {c : Cfg} {l1 : List L1Ref} {safe : L2Ref} {incl : L1Ref}
    {b : SingleBatch} (h : batchValidity c l1 safe incl b = .accept) :
    ∀ tx ∈ b.txs, ∃ ty rest, tx = ty :: rest ∧ ty ≠ DEPOSIT_TX_TYPE := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hT⟩ := accept_sound h
  intro tx hmem
  have ht := hT tx hmem
  match tx, ht with
  | [], ht => simp [txAllowed] at ht
  | ty :: rest, ht =>
    refine ⟨ty, rest, rfl, fun hd => ?_⟩
    simp [txAllowed, hd] at ht

/-! ## 4. Eager derivation is safe

  The spec's "Eager Block Derivation" section lets implementations decide batches
  before the whole sequencing window is available. That is only correct if a verdict
  reached early can never be revised by later L1 data. op-node and kona both carry a
  comment warning that otherwise "the eager algorithm may diverge from a non-eager
  algorithm". These theorems discharge that obligation for the rule itself. -/

/-- Once `next_epoch` is known, the rule always reaches a verdict. -/
theorem core_decided_with_next (c : Cfg) (epoch next : L1Ref) (safe : L2Ref)
    (incl : L1Ref) (b : SingleBatch) :
    batchValidityCore c epoch (some next) safe incl b ≠ .undecided := by
  unfold batchValidityCore
  dsimp only
  by_cases h1 : safe.time + c.blockTime < b.time
  · rw [if_pos h1]; cases c.holocene incl.time <;> simp
  rw [if_neg h1]
  by_cases h2 : b.time < safe.time + c.blockTime
  · rw [if_pos h2]; cases c.holocene incl.time <;> simp
  rw [if_neg h2]
  by_cases h3 : b.parentHash ≠ safe.hash
  · rw [if_pos h3]; simp
  rw [if_neg h3]
  by_cases h4 : b.epochNum + c.seqWindowSize < incl.num
  · rw [if_pos h4]; simp
  rw [if_neg h4]
  by_cases h5 : b.epochNum < epoch.num
  · rw [if_pos h5]; simp
  rw [if_neg h5]
  by_cases h6 : epoch.num + 1 < b.epochNum
  · rw [if_pos h6]; simp
  rw [if_neg h6]
  have hO : (if b.epochNum = epoch.num then some epoch else some next) =
      some (if b.epochNum = epoch.num then epoch else next) := by
    split <;> rfl
  rw [hO]
  dsimp only
  generalize (if b.epochNum = epoch.num then epoch else next) = origin
  by_cases h7 : b.epochHash ≠ origin.hash
  · rw [if_pos h7]; simp
  rw [if_neg h7]
  by_cases h8 : b.time < origin.time
  · rw [if_pos h8]; simp
  rw [if_neg h8]
  by_cases h9 : origin.time + c.maxDrift origin.time < b.time
  · rw [if_pos h9]
    by_cases h10 : b.txs ≠ []
    · rw [if_pos h10]; simp
    rw [if_neg h10]
    by_cases he : b.epochNum = epoch.num
    · rw [if_pos he]
      by_cases h11 : next.time ≤ b.time
      · rw [if_pos h11]; simp
      · rw [if_neg h11]; exact txChecks_ne_undecided c b
    · rw [if_neg he]; exact txChecks_ne_undecided c b
  · rw [if_neg h9]; exact txChecks_ne_undecided c b

/-- A verdict reached without `next_epoch` is unchanged once `next_epoch` arrives. -/
theorem core_eager_stable {c : Cfg} {epoch : L1Ref} {safe : L2Ref} {incl : L1Ref}
    {b : SingleBatch} (next : L1Ref)
    (h : batchValidityCore c epoch none safe incl b ≠ .undecided) :
    batchValidityCore c epoch (some next) safe incl b =
      batchValidityCore c epoch none safe incl b := by
  unfold batchValidityCore at h ⊢
  dsimp only at h ⊢
  by_cases h1 : safe.time + c.blockTime < b.time
  · simp only [if_pos h1]
  simp only [if_neg h1] at h ⊢
  by_cases h2 : b.time < safe.time + c.blockTime
  · simp only [if_pos h2]
  simp only [if_neg h2] at h ⊢
  by_cases h3 : b.parentHash ≠ safe.hash
  · simp only [if_pos h3]
  simp only [if_neg h3] at h ⊢
  by_cases h4 : b.epochNum + c.seqWindowSize < incl.num
  · simp only [if_pos h4]
  simp only [if_neg h4] at h ⊢
  by_cases h5 : b.epochNum < epoch.num
  · simp only [if_pos h5]
  simp only [if_neg h5] at h ⊢
  by_cases h6 : epoch.num + 1 < b.epochNum
  · simp only [if_pos h6]
  simp only [if_neg h6] at h ⊢
  by_cases he : b.epochNum = epoch.num
  · -- sticking to the current epoch: `next_epoch` is consulted only in the drift branch
    simp only [if_pos he] at h ⊢
    by_cases h7 : b.epochHash ≠ epoch.hash
    · simp only [if_pos h7]
    simp only [if_neg h7] at h ⊢
    by_cases h8 : b.time < epoch.time
    · simp only [if_pos h8]
    simp only [if_neg h8] at h ⊢
    by_cases h9 : epoch.time + c.maxDrift epoch.time < b.time
    · simp only [if_pos h9] at h ⊢
      by_cases h10 : b.txs ≠ []
      · simp only [if_pos h10]
      simp only [if_neg h10] at h
      exact absurd rfl h
    · simp only [if_neg h9]
  · -- advancing the epoch without `next_epoch` is always undecided
    simp only [if_neg he] at h
    exact absurd rfl h

/-- Over the slice: with two or more L1 blocks the verdict is never `undecided`… -/
theorem undecided_needs_more_l1 {c : Cfg} {l1 : List L1Ref} {safe : L2Ref}
    {incl : L1Ref} {b : SingleBatch}
    (h : batchValidity c l1 safe incl b = .undecided) : l1.length < 2 := by
  match l1, h with
  | [], _ => simp
  | [_], _ => simp
  | e :: n :: _, h => exact absurd h (core_decided_with_next c e n safe incl b)

/-- …and appending further L1 blocks never changes a decided verdict. -/
theorem eager_stable {c : Cfg} {l1 : List L1Ref} {safe : L2Ref} {incl : L1Ref}
    {b : SingleBatch} (more : List L1Ref)
    (h : batchValidity c l1 safe incl b ≠ .undecided) :
    batchValidity c (l1 ++ more) safe incl b = batchValidity c l1 safe incl b := by
  match l1, more, h with
  | [], _, h => exact absurd rfl h
  | [_], [], _ => rfl
  | [_], n :: _, h => exact core_eager_stable n h
  | _ :: _ :: _, _, _ => rfl

/-! ## 5. Spec gap: the prose and both clients disagree on unassigned tx types -/

/-- A batch carrying a type-0x03 transaction (or any other unassigned type) is
    accepted by op-node and kona, but must be dropped under a literal reading of
    "any transaction of a future type > 2". -/
theorem spec_gap_type3 (c : Cfg) (t : Nat) (rest : List UInt8) :
    txAllowed c t (0x03 :: rest) = true ∧ txAllowedProse c t (0x03 :: rest) = false := by
  constructor <;> rfl

end OpDerivation
