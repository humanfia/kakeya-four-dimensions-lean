/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/TestedSequence.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.TestedSample

/-! Sequence interface adapted from this LOT tree, o156/x0524,
TestedSample.lean c7cfd90. -/

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep

open MeasureTheory Set Filter

/-- The exact sequence predicate, with each finite sample packaged as a record. -/
noncomputable def TestedSequence (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) : Prop :=
  (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ 0 < L ∧ (∀ k γ, 0 ≤ ω k γ) ∧ (∀ k, (∑ γ, ω k γ) = 1) ∧ (∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ)) ∧ (∃ Mb : ℕ, ∀ k γ, 0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb) ∧ (∃ Me De : ℕ, ∀ k γ, MeasurableSet (E k γ) ∧ ∀ i, fmt 7 (N k ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E k γ}) ∧
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      Nonempty (TestedSample cv lam (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D ε)

/-- The expanded existential interface used in the frozen split statement. -/
noncomputable def TestedSequenceRaw (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) : Prop :=
  (∀ k, 2 ≤ N k) ∧ Filter.Tendsto N Filter.atTop Filter.atTop ∧ 0 < L ∧ (∀ k γ, 0 ≤ ω k γ) ∧ (∀ k, (∑ γ, ω k γ) = 1) ∧ (∀ k γ, MeasureTheory.IsProbabilityMeasure (ν k γ)) ∧ (∃ Mb : ℕ, ∀ k γ, 0 < B k γ ∧ B k γ ≤ N k ^ Mb ∧ (B k γ)⁻¹ ≤ N k ^ Mb) ∧ (∃ Me De : ℕ, ∀ k γ, MeasurableSet (E k γ) ∧ ∀ i, fmt 7 (N k ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E k γ}) ∧
    ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
      TestedAt cv lam (N k) (W k) (ω k) (ν k) (E k) (B k) L dc a h M D ε

/-- Packaging finite samples as records preserves the exact sequence predicate. -/
theorem testedSequence_iff_raw (cv : Prop) (lam : ℝ) (N : ℕ → ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → Measure Trajectory)
    (E : (k : ℕ) → Fin (W k) → Set Incidence) (B : (k : ℕ) → Fin (W k) → ℝ)
    (L dc a h : ℝ) :
    TestedSequence cv lam N W ω ν E B L dc a h ↔
      TestedSequenceRaw cv lam N W ω ν E B L dc a h := by
  simp only [TestedSequence, TestedSequenceRaw, sample_nonempty_iff]

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep
