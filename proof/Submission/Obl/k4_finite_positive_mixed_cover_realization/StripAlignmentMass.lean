/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/StripAlignmentMass.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripAlignment

/-!
Original candidate coverage survives after discarding pairs of strips charged
to deeper reference laws. The laws and their parent multiplicities are kept
separate; no new conditional probability is introduced in this step.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set

/-- An incidence with no aligned deeper chart is charged under any deeper
chart that contains it. Subadditivity suffices even for nonmeasurable witness
sets and overlapping deeper charts. -/
theorem aligned_original_mass_le {Ω A D P : Type*} [MeasurableSpace Ω]
    [Fintype A] [Fintype D] [DecidableEq P]
    (μ : A → Measure Ω) (reference : D → Measure Ω)
    (H : A → Set Ω) (deep : D → Set Ω) (aligned : A → D → Prop)
    (parent : A → P) (ancestor : D → P) (B : D → ENNReal) (C : ENNReal)
    (hcover : ∀ a, H a ⊆ ⋃ d, deep d)
    (hdom : ∀ a d, ¬ aligned a d → μ a (H a ∩ deep d) ≤ reference d (H a ∩ deep d))
    (hzero : ∀ a d, parent a ≠ ancestor d → reference d (H a ∩ deep d) = 0)
    (hbound : ∀ a d, parent a = ancestor d → ¬ aligned a d →
      reference d (H a ∩ deep d) ≤ B d)
    (hcard : ∀ d,
      ((Finset.univ.filter (fun a => parent a = ancestor d)).card : ENNReal) ≤ C) :
    (∑ a, μ a (H a)) ≤
      (∑ a, μ a (H a ∩ {p | ∃ d, aligned a d ∧ p ∈ deep d})) + C * ∑ d, B d := by
  classical
  let S : A → D → Set Ω := fun a d => if aligned a d then ∅ else H a ∩ deep d
  have hcharge : (∑ d, ∑ a, reference d (S a d)) ≤ C * ∑ d, B d := by
    apply sum_parented_charges_le reference parent ancestor S B C hcard
    · intro a d hne
      by_cases ha : aligned a d
      · simp only [S, ite_eq_left ha, measure_empty]
      · simpa only [S, ite_eq_right ha] using hzero a d hne
    · intro a d heq
      by_cases ha : aligned a d
      · simp only [S, ite_eq_left ha, measure_empty, zero_le]
      · simpa only [S, ite_eq_right ha] using hbound a d heq ha
  have hdomS (a : A) (d : D) : μ a (S a d) ≤ reference d (S a d) := by
    by_cases ha : aligned a d
    · simp only [S, ite_eq_left ha, measure_empty, le_refl]
    · simpa only [S, ite_eq_right ha] using hdom a d ha
  have hmass (a : A) : μ a (H a) ≤
      μ a (H a ∩ {p | ∃ d, aligned a d ∧ p ∈ deep d}) + ∑ d, μ a (S a d) := by
    have hsub : H a ⊆
        (H a ∩ {p | ∃ d, aligned a d ∧ p ∈ deep d}) ∪ ⋃ d, S a d := by
      intro p hp
      obtain ⟨d, hd⟩ := mem_iUnion.mp (hcover a hp)
      by_cases ha : aligned a d
      · exact Or.inl ⟨hp, d, ha, hd⟩
      · apply Or.inr
        apply mem_iUnion.mpr
        refine ⟨d, ?_⟩
        dsimp only [S]
        rw [ite_eq_right ha]
        exact ⟨hp, hd⟩
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl (measure_iUnion_fintype_le _ _)))
  calc
    _ ≤ ∑ a, (μ a (H a ∩ {p | ∃ d, aligned a d ∧ p ∈ deep d}) + ∑ d, μ a (S a d)) :=
      Finset.sum_le_sum fun a _ => hmass a
    _ = (∑ a, μ a (H a ∩ {p | ∃ d, aligned a d ∧ p ∈ deep d})) +
        ∑ d, ∑ a, μ a (S a d) := by rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ (∑ a, μ a (H a ∩ {p | ∃ d, aligned a d ∧ p ∈ deep d})) +
        ∑ d, ∑ a, reference d (S a d) := by
      exact add_le_add le_rfl (Finset.sum_le_sum fun d _ =>
        Finset.sum_le_sum fun a _ => hdomS a d)
    _ ≤ _ := add_le_add le_rfl hcharge

end Submission.Obl.k4_finite_positive_mixed_cover_realization
