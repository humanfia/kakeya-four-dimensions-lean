/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/CommonScaleMasks.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.FiniteScaleGrid

/-! Common finite-scale masks and exact membership in the tested exponent grid. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem positiveScaleGrid_mem_bounds {M L : ℕ} (hM : 0 < M) {r : ℝ}
    (hr : r ∈ positiveScaleGrid M L) :
    1 / (M : ℝ) ≤ r ∧ r ≤ (L : ℝ) ∧ ∃ m : ℕ, r = (m : ℝ) / (M : ℝ) := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hr
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hm).1) hMpos.le,
    (div_le_iff₀ hMpos).mpr ?_, m, rfl⟩
  exact_mod_cast (Finset.mem_Icc.mp hm).2

theorem mem_positiveScaleGrid_of_grid_scale {M L : ℕ} (hM : 0 < M) {r : ℝ}
    (hr : 0 < r) (hrL : r ≤ (L : ℝ)) (hgrid : ∃ m : ℕ, r = (m : ℝ) / (M : ℝ)) :
    r ∈ positiveScaleGrid M L := by
  obtain ⟨m, rfl⟩ := hgrid
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hmpos : 0 < m := by
    by_contra hm
    have hm₀ : m = 0 := Nat.eq_zero_of_not_pos hm
    simpa only [hm₀, Nat.cast_zero, zero_div, lt_self_iff_false] using hr
  have hmL : m ≤ L * M := by
    exact_mod_cast (div_le_iff₀ hMpos).mp hrL
  exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨hmpos,hmL⟩, rfl⟩

theorem scalarStageGrid_card_le (j : ℕ) : (positiveScaleGrid (j ^ 2) j).card ≤ j ^ 3 :=
  (positiveScaleGrid_card_le _ _).trans_eq (by ring)

theorem scalarStage_compact_bounds {J : ℕ} (hJ : 2 ≤ J) :
    1 < 100 * (J : ℝ) ^ 2 ∧
    (100 * (J : ℝ) ^ 2)⁻¹ ≤ 1 / (J : ℝ) ∧ 1 / (J : ℝ) ≤ 100 * (J : ℝ) ^ 2 ∧
    ∀ r ∈ positiveScaleGrid (J ^ 2) J,
      (100 * (J : ℝ) ^ 2)⁻¹ ≤ r ∧ r ≤ 100 * (J : ℝ) ^ 2 ∧
      (100 * (J : ℝ) ^ 2)⁻¹ ≤ 10 * r ∧ 10 * r ≤ 100 * (J : ℝ) ^ 2 := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJ₁ : (1 : ℝ) ≤ J := by exact_mod_cast (by omega : 1 ≤ J)
  have hJ2 : 1 ≤ (J : ℝ) ^ 2 := one_le_pow₀ hJ₁
  have hJJ : (J : ℝ) ≤ (J : ℝ) ^ 2 := by nlinarith
  have hR : 1 < 100 * (J : ℝ) ^ 2 := by nlinarith
  have hi : (100 * (J : ℝ) ^ 2)⁻¹ ≤ 1 / (J : ℝ) ^ 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hJpos 2)
      (show (J : ℝ) ^ 2 ≤ 100 * (J : ℝ) ^ 2 by nlinarith [sq_nonneg (J : ℝ)])
  have hb : 1 / (J : ℝ) ^ 2 ≤ 1 / (J : ℝ) := one_div_le_one_div_of_le hJpos hJJ
  have hb₁ : 1 / (J : ℝ) ≤ 1 := (div_le_one hJpos).mpr hJ₁
  refine ⟨hR, hi.trans hb, hb₁.trans hR.le, ?_⟩
  intro r hr
  have hrange := positiveScaleGrid_mem_bounds (show 0 < J ^ 2 from pow_pos (by omega) 2) hr
  have hl : 1 / (J : ℝ) ^ 2 ≤ r := by simpa only [Nat.cast_pow] using hrange.1
  have hrpos : 0 < r := (by positivity : 0 < 1 / (J : ℝ) ^ 2).trans_le hl
  refine ⟨hi.trans hl, ?_, (hi.trans hl).trans (by linarith), ?_⟩
  · linarith [hrange.2.1]
  · nlinarith [hrange.2.1]

/-- Intersect all finitely many masks while charging every omission to the original
measure. The returned set is literally a subset of every preceding mask. -/
theorem exists_common_finite_core {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i)) (ε : ι → ℝ≥0∞)
    (hloss : ∀ i, μ (A \ E i) ≤ ε i) :
    ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ A ∧ (∀ i, F ⊆ E i) ∧
      μ (A \ F) ≤ ∑ i, ε i := by
  let F := A ∩ ⋂ i, E i
  have hF : MeasurableSet F := hA.inter (MeasurableSet.iInter hE)
  have hsub : A \ F ⊆ ⋃ i, A \ E i := by
    intro p hp
    have hnot : ¬ ∀ i, p ∈ E i := by
      intro hall
      exact hp.2 ⟨hp.1, Set.mem_iInter.mpr hall⟩
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Set.mem_iUnion.mpr ⟨i,hp.1,hi⟩
  refine ⟨F, hF, inter_subset_left, fun i p hp => Set.mem_iInter.mp hp.2 i, ?_⟩
  exact (measure_mono hsub).trans ((measure_iUnion_fintype_le μ (fun i => A \ E i)).trans
    (Finset.sum_le_sum fun i hi => hloss i))

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
