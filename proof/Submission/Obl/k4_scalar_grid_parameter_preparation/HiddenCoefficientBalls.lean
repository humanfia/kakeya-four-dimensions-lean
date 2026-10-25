/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/HiddenCoefficientBalls.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientPriorCaps
import Submission.Obl.k4_lifted_plank_cap_saturation.Bins

/-! Hidden-coefficient ball caps inside a fixed original affine bin. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

def scalarHiddenCoefficients (a : Fin 5 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![a 2,a 3,a 4]

theorem affine_hidden_coefficient_ball_cap {X : Type*} [MeasurableSpace X]
    (θ : Measure X) (a : X → Fin 5 → ℝ) (π : Measure ℝ) [IsFiniteMeasure π]
    (ξ ζ L : ℝ) (hζ : 0 < ζ) (hL : 0 ≤ L) (q c : ℤ)
    (hcap : ∀ z : Fin 5 → ℤ, θ {l | scalarMixedCoefficientTag ξ ζ (a l) = z} ≤
      ENNReal.ofReal L * π (scalarVelocityBin ξ (z 1))) (b : EuclideanSpace ℝ (Fin 3)) :
    θ {l | scalarHiddenCoefficients (a l) ∈ Metric.ball b ζ ∧
      (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c} ≤
        ENNReal.ofReal (216 * L) * π (scalarVelocityBin ξ c) := by
  let G := {l | (⌊a l 0 / ξ⌋ : ℤ) = q ∧ a l 1 ∈ scalarVelocityBin ξ c}
  let T := L * (π (scalarVelocityBin ξ c)).toReal
  have hbin (z : Fin 3 → ℤ) : θ {l |
      (∀ j : Fin 3, (⌊scalarHiddenCoefficients (a l) j / ζ⌋ : ℤ) = z j) ∧ l ∈ G} ≤
        ENNReal.ofReal T := by
    let full : Fin 5 → ℤ := ![q,c,z 0,z 1,z 2]
    calc
      _ ≤ θ {l | scalarMixedCoefficientTag ξ ζ (a l) = full} := measure_mono (by
        intro l hl
        ext e
        fin_cases e
        · simpa [scalarMixedCoefficientTag,full] using hl.2.1
        · simpa [scalarMixedCoefficientTag,scalarVelocityBin,full] using hl.2.2
        · simpa [scalarMixedCoefficientTag,scalarHiddenCoefficients,full] using hl.1 0
        · simpa [scalarMixedCoefficientTag,scalarHiddenCoefficients,full] using hl.1 1
        · simpa [scalarMixedCoefficientTag,scalarHiddenCoefficients,full] using hl.1 2)
      _ ≤ ENNReal.ofReal L * π (scalarVelocityBin ξ c) := by simpa only [full,Matrix.cons_val_one,Matrix.cons_val_zero] using hcap full
      _ = _ := by dsimp [T]; rw [ENNReal.ofReal_mul hL,ENNReal.ofReal_toReal (measure_ne_top π _)]
  have hh := Submission.Obl.k4_lifted_plank_cap_saturation.coefficient_ball_mass_le_of_bin_bounds
    θ (fun l => scalarHiddenCoefficients (a l)) G b hζ.le hζ (mul_nonneg hL ENNReal.toReal_nonneg) hbin
  have hconst : (4 * ζ / ζ + 2) ^ 3 = (216 : ℝ) := by field_simp; norm_num
  calc
    _ ≤ ENNReal.ofReal (216 * T) := by simpa only [hconst,G,Set.mem_ofPred_eq,T] using hh
    _ = ENNReal.ofReal ((216 * L) * (π (scalarVelocityBin ξ c)).toReal) := by congr 1; dsimp [T]; ring
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal (measure_ne_top π _)]

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
