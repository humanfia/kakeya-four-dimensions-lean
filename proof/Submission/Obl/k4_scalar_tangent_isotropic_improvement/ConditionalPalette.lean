import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PaletteSampling

/-! Conditional cell caps retain mass in the fixed original palette. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

/-- A positive state cannot be supported on a small part of the original
palette when its joint masses satisfy the conditional ceiling. -/
theorem palette_support_mass {β : Type*} [Fintype β]
    (a w : β → ℝ) {H m : ℝ} (hH : 0 < H) (hm : 0 < m)
    (hcover : m ≤ ∑ j, a j) (hcap : ∀ j, a j ≤ H * m * w j) :
    H⁻¹ ≤ ∑ j, if 0 < a j then w j else 0 := by
  have hbound : m ≤ H * m * (∑ j, if 0 < a j then w j else 0) := by
    calc
      m ≤ ∑ j, a j := hcover
      _ ≤ ∑ j, H * m * (if 0 < a j then w j else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hpos : 0 < a j
        · simpa only [ite_eq_left hpos] using hcap j
        · simp only [ite_eq_right hpos, mul_zero]
          exact le_of_not_gt hpos
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hcancel : 1 ≤ H * (∑ j, if 0 < a j then w j else 0) :=
    (mul_le_mul_iff_right₀ hm).mp (by nlinarith only [hbound])
  rw [← one_div]
  apply (div_le_iff₀ hH).mpr
  nlinarith only [hcancel]

theorem original_palette_weights_subprobability {β X : Type*} [Fintype β]
    [MeasurableSpace X] (π : Measure X) [IsProbabilityMeasure π] (B : β → Set X)
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise fun i j => Disjoint (B i) (B j)) :
    (∑ j, (π (B j)).toReal) ≤ 1 := by
  have hdisj : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint B := by
    intro i hi j hj hij
    exact hd hij
  have hsum : ∑ j, π (B j) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj (fun j hj => hB j)]
    exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ (μ := π))
  have h := ENNReal.toReal_mono (by norm_num) hsum
  rw [ENNReal.toReal_sum (fun j hj => measure_ne_top π (B j))] at h
  simpa only [ENNReal.toReal_one] using h

/-- Finite palette discretization uses the original palette weights, including
when palette mass lies outside the finite collection of used velocity bins. -/
theorem palette_support_mass_of_measure_caps {Ω β X : Type*} [Fintype β]
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Measure X) [IsFiniteMeasure π]
    (C : Set Ω) (V : Ω → X) (B : β → Set X) {H : ℝ} (hH : 0 < H)
    (hpos : 0 < μ C)
    (hcover : μ C ≤ ∑ j, μ (C ∩ V ⁻¹' B j))
    (hcap : ∀ j, μ (C ∩ V ⁻¹' B j) ≤ ENNReal.ofReal H * μ C * π (B j)) :
    H⁻¹ ≤ ∑ j, if 0 < (μ (C ∩ V ⁻¹' B j)).toReal then (π (B j)).toReal else 0 := by
  apply palette_support_mass
    (fun j => (μ (C ∩ V ⁻¹' B j)).toReal) (fun j => (π (B j)).toReal)
    hH (ENNReal.toReal_pos hpos.ne' (measure_ne_top μ C))
  · have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j hj => measure_ne_top μ _)) hcover
    rwa [ENNReal.toReal_sum (fun j hj => measure_ne_top μ _)] at h
  · intro j
    have h := ENNReal.toReal_mono (by finiteness) (hcap j)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH.le] using h

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
