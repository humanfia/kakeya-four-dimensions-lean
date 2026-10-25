/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/AffineFrostman.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineRestrictedPrior
import Submission.Obl.k4_scalar_grid_parameter_preparation.AffineCoefficientCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.FrostmanExtension

/-! One coarse hidden width gives both total-mass and all-radius Frostman ceilings. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

theorem restricted_affine_prior_frostman {X : Type*} [MeasurableSpace X]
    (θ ν : Measure X) (a : X → Fin 5 → ℝ) (ha : Measurable a) (π : Measure ℝ) [IsFiniteMeasure π]
    (ξ σ B H d : ℝ) (hξ : 0 < ξ) (hσ : 0 < σ) (hξσ : ξ ≤ σ) (hσ₁ : σ ≤ 1)
    (hB : 1 ≤ B) (hH : 0 ≤ H) (hd : 0 ≤ d) (q c : ℤ)
    (hbounded : ∀ᵐ l ∂θ, ∀ e, |a l e| ≤ B)
    (hν : ν ≤ θ.restrict (scalarAffineCoefficientCell a ξ q c))
    (hcap : ∀ ζ : ℝ, ξ ≤ ζ → ζ ≤ σ → ∀ z : Fin 5 → ℤ,
      θ {l | scalarMixedCoefficientTag ξ ζ (a l) = z} ≤
        ENNReal.ofReal (H * ξ * ζ ^ d) * π (scalarVelocityBin ξ (z 1))) :
    let p := ENNReal.ofReal ξ * π (scalarVelocityBin ξ c)
    let Q := (6 * B / σ) ^ 3 * H
    ν Set.univ ≤ p * ENNReal.ofReal Q ∧
      ∀ b r, ξ ≤ r → ν {l | boundedScalarHiddenCoefficients B (a l) ∈ Metric.ball b r} ≤
        p * ENNReal.ofReal (Q * r ^ d) := by
  let p := ENNReal.ofReal ξ * π (scalarVelocityBin ξ c)
  let M := (6 * B / σ) ^ 3
  let Q := M * H
  let A := Q * σ ^ d
  change ν Set.univ ≤ p * ENNReal.ofReal Q ∧ _
  have hM : 0 ≤ M := pow_nonneg (div_nonneg (mul_nonneg (by norm_num)
    (zero_le_one.trans hB)) hσ.le) 3
  have hQ : 0 ≤ Q := mul_nonneg hM hH
  have hA : 0 ≤ A := mul_nonneg hQ (Real.rpow_nonneg hσ.le _)
  have hνtotal : ν Set.univ ≤ θ (scalarAffineCoefficientCell a ξ q c) := by
    simpa only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hν Set.univ
  have hAff := affine_coefficient_prior_cap θ a ξ σ B hσ hσ₁ hB hbounded π
    (ENNReal.ofReal (H * ξ * σ ^ d)) q c (hcap σ hξσ le_rfl)
  have htotal : ν Set.univ ≤ p * ENNReal.ofReal A := by
    calc
      _ ≤ θ (scalarAffineCoefficientCell a ξ q c) := hνtotal
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (H * ξ * σ ^ d) * π (scalarVelocityBin ξ c) := hAff
      _ = ENNReal.ofReal (M * (H * ξ * σ ^ d)) * π (scalarVelocityBin ξ c) := by
        rw [← ENNReal.ofReal_mul hM]
      _ = ENNReal.ofReal (ξ * A) * π (scalarVelocityBin ξ c) := by
        have he : M * (H * ξ * σ ^ d) = ξ * A := by dsimp [A,Q]; ring
        rw [he]
      _ = _ := by rw [ENNReal.ofReal_mul hξ.le]; dsimp [p]; ring
  have hfine (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : ξ ≤ r) (hrσ : r ≤ σ) :
      ν {l | boundedScalarHiddenCoefficients B (a l) ∈ Metric.ball b r} ≤
        p * ENNReal.ofReal ((216 * H) * r ^ d) := by
    have hrpos : 0 < r := hξ.trans_le hr
    have hh := restricted_affine_hidden_ball_cap θ ν a ha π ξ r B (H * ξ * r ^ d)
      hrpos (mul_nonneg (mul_nonneg hH hξ.le) (Real.rpow_nonneg hrpos.le _)) q c hbounded hν
      (hcap r hr hrσ) b
    apply hh.trans_eq
    have he : 216 * (H * ξ * r ^ d) = ξ * ((216 * H) * r ^ d) := by ring
    rw [he,ENNReal.ofReal_mul hξ.le]
    dsimp [p]
    ring
  have hCQ : 216 * H ≤ Q := by
    have hratio : 1 ≤ B / σ := (one_le_div hσ).mpr (hσ₁.trans hB)
    have hsix : (6 : ℝ) ≤ 6 * B / σ := by
      have he : 6 * B / σ = 6 * (B / σ) := by ring
      rw [he]
      linarith
    have hMc : (216 : ℝ) ≤ M := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hsix 3
      norm_num at hh
      exact hh
    exact mul_le_mul_of_nonneg_right hMc hH
  have hAQ : A * σ ^ (-d) ≤ Q := by
    dsimp [A]
    rw [mul_assoc,← Real.rpow_add hσ]
    simp
  refine ⟨htotal.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)),?_⟩
  · have hpow : σ ^ d ≤ 1 := by simpa only [Real.one_rpow] using Real.rpow_le_rpow hσ.le hσ₁ hd
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hQ
  · exact original_ball_cap_extension ν (fun l => boundedScalarHiddenCoefficients B (a l)) p
      ξ σ d A (216 * H) Q hξ hσ hd hA htotal hfine hCQ hAQ

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
