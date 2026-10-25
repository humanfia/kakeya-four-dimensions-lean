import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

/-- Recovering each selected chart on a list of size at most K controls its
chart-wise mass by K times the mass of the selected union. -/
lemma sparse_list_union_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (C : ι → Set X) (hC : ∀ i, MeasurableSet (C i))
    (Λ : X → Finset ι) (K : ENNReal) (hK : ∀ x, ((Λ x).card : ENNReal) ≤ K)
    (hrec : ∀ i, μ {x | x ∈ C i ∧ i ∉ Λ x} = 0) :
    ∑ i, μ (C i) ≤ K * μ (⋃ i, C i) := by
  classical
  have hae : ∀ᵐ x ∂μ, ∀ i, x ∈ C i → i ∈ Λ x := by
    apply ae_all_iff.mpr
    intro i
    rw [ae_iff]
    simpa only [not_imp, not_not] using hrec i
  calc
    ∑ i, μ (C i) = ∫⁻ x, ∑ i, (C i).indicator (fun _ => (1 : ENNReal)) x ∂μ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        simpa only [one_mul] using (lintegral_indicator_const (hC i) 1).symm
      · intro i _
        exact measurable_const.indicator (hC i)
    _ ≤ ∫⁻ x, (⋃ i, C i).indicator (fun _ => K) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hae] with x hx
      by_cases hmem : x ∈ ⋃ i, C i
      · rw [indicator_of_mem hmem]
        have hsub : Finset.univ.filter (fun i => x ∈ C i) ⊆ Λ x := by
          intro i hi
          exact hx i (Finset.mem_filter.mp hi).2
        calc
          ∑ i, (C i).indicator (fun _ => (1 : ENNReal)) x =
              ((Finset.univ.filter (fun i => x ∈ C i)).card : ENNReal) := by
            simp [Set.indicator, Finset.sum_boole]
          _ ≤ ((Λ x).card : ENNReal) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ K := hK x
      · have hn i : x ∉ C i := fun hi => hmem (mem_iUnion.mpr ⟨i, hi⟩)
        simp only [indicator_of_notMem hmem, indicator_of_notMem (hn _), Finset.sum_const_zero, le_refl]
    _ = K * μ (⋃ i, C i) := lintegral_indicator_const (MeasurableSet.iUnion hC) K

lemma weighted_sparse_list_union_mass {X ι Γ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype Γ]
    (μ : Γ → Measure X) (w : Γ → ENNReal) (γ : ι → Γ)
    (C : ι → Set X) (hC : ∀ i, MeasurableSet (C i))
    (Λ : Γ → X → Finset ι) (K : ENNReal) (hK : ∀ g x, ((Λ g x).card : ENNReal) ≤ K)
    (hrec : ∀ i, μ (γ i) {x | x ∈ C i ∧ i ∉ Λ (γ i) x} = 0) :
    (∑ i, w (γ i) * μ (γ i) (C i)) ≤
      K * ∑ g, w g * μ g {x | ∃ i, γ i = g ∧ x ∈ C i} := by
  classical
  let D : Γ → ι → Set X := fun g i => if γ i = g then C i else ∅
  have hDm g i : MeasurableSet (D g i) := by
    dsimp [D]
    split_ifs
    · exact hC i
    · exact MeasurableSet.empty
  have hrecD g i : μ g {x | x ∈ D g i ∧ i ∉ Λ g x} = 0 := by
    by_cases hi : γ i = g
    · subst g
      simpa only [D, ite_true] using hrec i
    · simp only [D, ite_eq_right hi, mem_empty_iff_false, false_and, ofPred_false, measure_empty]
  have hsum g := sparse_list_union_mass (μ g) (D g) (hDm g) (Λ g) K (hK g) (hrecD g)
  have hunion g : (⋃ i, D g i) = {x | ∃ i, γ i = g ∧ x ∈ C i} := by
    ext x
    simp [D]
  calc
    _ = ∑ g, w g * ∑ i, μ g (D g i) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [D, apply_ite, measure_empty, mul_zero]
      simp [eq_comm]
    _ ≤ ∑ g, w g * (K * μ g (⋃ i, D g i)) := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul' le_rfl (hsum g)
    _ = K * ∑ g, w g * μ g {x | ∃ i, γ i = g ∧ x ∈ C i} := by
      simp_rw [hunion, ← mul_assoc, mul_comm (w _) K, mul_assoc]
      rw [Finset.mul_sum]

end Submission.Obl.k4_scalar_normalized_exact_refinement
