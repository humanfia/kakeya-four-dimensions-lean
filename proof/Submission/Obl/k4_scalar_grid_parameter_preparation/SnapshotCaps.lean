/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/SnapshotCaps.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.TraceRectangle

/-! Integrate fixed-time caps and sum the bounded grid lists of a coefficient block. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem integrated_snapshot_mass_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (Z : Set (X × ℝ)) (hZ : MeasurableSet Z)
    (hunit : Z ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (C : Set X) (hC : MeasurableSet C) (B : ℝ≥0∞)
    (hcap : ∀ t ∈ Set.Icc (0 : ℝ) 1, ν {l | (l,t) ∈ Z ∧ l ∈ C} ≤ B) :
    ((ν.prod volume).restrict Z) (C ×ˢ Set.univ) ≤ B := by
  rw [Measure.restrict_apply (hC.prod MeasurableSet.univ),
    Measure.prod_apply_symm ((hC.prod MeasurableSet.univ).inter hZ)]
  calc
    _ ≤ ∫⁻ t, (Set.Icc (0 : ℝ) 1).indicator (fun _ => B) t ∂volume := by
      apply lintegral_mono
      intro t
      change ν ((fun l => (l,t)) ⁻¹' ((C ×ˢ Set.univ) ∩ Z)) ≤
        (Set.Icc (0 : ℝ) 1).indicator (fun _ => B) t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · have he : (fun l => (l,t)) ⁻¹' ((C ×ˢ Set.univ) ∩ Z) =
            {l | (l,t) ∈ Z ∧ l ∈ C} := by
          ext l
          simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ,
            true_and, mem_ofPred_eq, and_comm]
        rw [he, Set.indicator_of_mem ht]
        exact hcap t ht
      · have he : (fun l => (l,t)) ⁻¹' ((C ×ˢ Set.univ) ∩ Z) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro l hl
          exact ht (hunit hl.2).2
        simp only [he, measure_empty, Set.indicator_of_notMem ht, le_refl]
    _ = B := by simp [lintegral_indicator measurableSet_Icc]

/-- At a fixed time a mixed coefficient block has boundedly many position bins.
Its palette bin is kept exactly; no relation between neighboring palette masses is used. -/
theorem two_coordinate_grid_mass_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Y V : X → ℝ) (Z : X → ℝ) (C : Set X) (P : Set ℝ)
    (ξ ζ : ℝ) (hξ : 0 < ξ) (hζ : 0 < ζ) (B : ℝ≥0∞)
    (hY : ∀ l ∈ C, ∀ l' ∈ C, dist (Y l) (Y l') ≤ 9 * ξ)
    (hZ : ∀ l ∈ C, ∀ l' ∈ C, dist (Z l) (Z l') ≤ 9 * ζ)
    (hV : ∀ l ∈ C, V l ∈ P)
    (hcap : ∀ q a : ℤ, μ {l | l ∈ C ∧ Y l ∈ scalarVelocityBin ξ q ∧
      Z l ∈ scalarVelocityBin ζ a ∧ V l ∈ P} ≤ B) :
    μ C ≤ 400 * B := by
  obtain ⟨hYf, hYc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Y '' C) (by positivity : 0 ≤ 9 * ξ) hξ 0 (by
      rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
      exact hY l hl l' hl')
  obtain ⟨hZf, hZc⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (Z '' C) (by positivity : 0 ≤ 9 * ζ) hζ 0 (by
      rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
      exact hZ l hl l' hl')
  simp only [sub_zero] at hYf hYc hZf hZc
  let J := hYf.toFinset
  let A := hZf.toFinset
  have hJ : (J.card : ℝ) ≤ 20 := by
    rw [← Set.ncard_eq_toFinset_card _ hYf]
    exact hYc.trans_eq (by field_simp; ring)
  have hA : (A.card : ℝ) ≤ 20 := by
    rw [← Set.ncard_eq_toFinset_card _ hZf]
    exact hZc.trans_eq (by field_simp; ring)
  let Cell : ℤ → ℤ → Set X := fun q a => {l | l ∈ C ∧ Y l ∈ scalarVelocityBin ξ q ∧
    Z l ∈ scalarVelocityBin ζ a ∧ V l ∈ P}
  have hcover : C ⊆ ⋃ q ∈ J, ⋃ a ∈ A, Cell q a := by
    intro l hl
    refine Set.mem_iUnion₂.mpr ⟨⌊Y l / ξ⌋, ?_,
      Set.mem_iUnion₂.mpr ⟨⌊Z l / ζ⌋, ?_, ⟨hl, rfl, rfl, hV l hl⟩⟩⟩
    · exact hYf.mem_toFinset.mpr ⟨Y l, ⟨l, hl, rfl⟩, rfl⟩
    · exact hZf.mem_toFinset.mpr ⟨Z l, ⟨l, hl, rfl⟩, rfl⟩
  have hm : μ C ≤ (J.card : ℝ≥0∞) * (A.card : ℝ≥0∞) * B := by
    calc
      _ ≤ μ (⋃ q ∈ J, ⋃ a ∈ A, Cell q a) := measure_mono hcover
      _ ≤ ∑ q ∈ J, ∑ a ∈ A, μ (Cell q a) := by
        apply (measure_biUnion_finset_le _ _).trans
        exact Finset.sum_le_sum fun q hq => measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ J, ∑ a ∈ A, B := by
        exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun a ha => hcap q a
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hc : J.card * A.card ≤ 400 := by
    have hh := mul_le_mul hJ hA (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 20)
    exact_mod_cast hh
  exact hm.trans (mul_le_mul (by exact_mod_cast hc) le_rfl bot_le bot_le)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
