/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PaletteWeightedCounts.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.VelocityBins

/-! Weighted counts of joint physical and original palette labels. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem sum_pair_palette_weights_le {P V : Type*} (S : Finset (P × V))
    (w : V → ℝ≥0∞) (hw : (∑ v ∈ S.image Prod.snd, w v) ≤ 1) :
    (∑ pv ∈ S, w pv.2) ≤ ((S.image Prod.fst).card : ℝ≥0∞) := by
  classical
  have hsub : S ⊆ (S.image Prod.fst) ×ˢ (S.image Prod.snd) := by
    intro pv hpv
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨pv,hpv,rfl⟩,
      Finset.mem_image.mpr ⟨pv,hpv,rfl⟩⟩
  calc
    _ ≤ ∑ pv ∈ (S.image Prod.fst) ×ˢ (S.image Prod.snd), w pv.2 :=
      Finset.sum_le_sum_of_subset hsub
    _ = ((S.image Prod.fst).card : ℝ≥0∞) * (∑ v ∈ S.image Prod.snd, w v) := by
      rw [Finset.sum_product]
      simp
    _ ≤ ((S.image Prod.fst).card : ℝ≥0∞) * 1 := mul_le_mul' le_rfl hw
    _ = _ := mul_one _

theorem sum_scalar_velocity_bin_masses_le_one (π : Measure ℝ) [IsProbabilityMeasure π]
    (ξ : ℝ) (V : Finset ℤ) : (∑ c ∈ V, π (scalarVelocityBin ξ c)) ≤ 1 := by
  have hd : (↑V : Set ℤ).PairwiseDisjoint (scalarVelocityBin ξ) :=
    fun i _ j _ hij => scalarVelocityBin_disjoint ξ hij
  calc
    _ = π (⋃ c ∈ V, scalarVelocityBin ξ c) :=
      (measure_biUnion_finset hd (fun c _ => measurableSet_scalarVelocityBin ξ c)).symm
    _ ≤ π Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem sum_joint_velocity_bin_masses_le {P : Type*} (π : Measure ℝ) [IsProbabilityMeasure π]
    (ξ : ℝ) (S : Finset (P × ℤ)) :
    (∑ pc ∈ S, π (scalarVelocityBin ξ pc.2)) ≤ ((S.image Prod.fst).card : ℝ≥0∞) :=
  sum_pair_palette_weights_le S _ (sum_scalar_velocity_bin_masses_le_one π ξ _)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
