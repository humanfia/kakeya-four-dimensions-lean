-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/StripWidthReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.StripReturn

namespace Submission.Obl.k4_finite_affine_candidate_return

noncomputable section

/-- The true relative determinant cancels the cumulative transverse
scale in a native strip. The first-row bound is the one supplied by
absence of an original candidate. The factor two permits recentering. -/
theorem strip_width_return_bound
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.det ≠ 0) (slope : ℝ)
    (N Nt t ℓ s v loss g J K A : ℝ) (hN : 0 < N) (hNt : Nt = N ^ t)
    (hK : 0 < K)
    (hrow : |M 0 0| + |M 0 1| ≤ 4 * J * N ^ g)
    (hdet : Nt ^ (-ℓ * s) / K ≤ |M.det|)
    (hallow : 8 * J * K * N ^ g * Nt ^ loss ≤ N ^ A) :
    2 * (Nt ^ loss * Nt ^ (-ℓ * s - v) / stripRowLength M slope) ≤
      N ^ A * N ^ (-(t * v)) := by
  have hNt0 : 0 < Nt := by rw [hNt]; positivity
  have hD := stripRowLength_pos M hM slope
  have hdetpos : 0 < Nt ^ (-ℓ * s) / K := by positivity
  have hbound := hdet.trans (det_le_stripRowLength M slope (4 * J * N ^ g) hrow)
  have hInv : (stripRowLength M slope)⁻¹ ≤ (4 * J * N ^ g) / (Nt ^ (-ℓ * s) / K) := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hD hdetpos).mpr
    simpa only [one_mul, mul_one, mul_comm] using hbound
  have hpow : Nt ^ (-ℓ * s - v) = Nt ^ (-ℓ * s) * Nt ^ (-v) := by
    rw [← Real.rpow_add hNt0]
    congr 1
  have hpow0 : Nt ^ (-ℓ * s) ≠ 0 := (Real.rpow_pos_of_pos hNt0 _).ne'
  calc
    _ = (2 * (Nt ^ loss * Nt ^ (-ℓ * s - v))) * (stripRowLength M slope)⁻¹ := by ring
    _ ≤ (2 * (Nt ^ loss * Nt ^ (-ℓ * s - v))) *
        ((4 * J * N ^ g) / (Nt ^ (-ℓ * s) / K)) :=
      mul_le_mul_of_nonneg_left hInv (by positivity)
    _ = (8 * J * K * N ^ g * Nt ^ loss) * Nt ^ (-v) := by
      rw [hpow]
      field_simp
      ring
    _ ≤ N ^ A * Nt ^ (-v) := mul_le_mul_of_nonneg_right hallow (by positivity)
    _ = _ := by
      rw [hNt, ← Real.rpow_mul hN.le]
      congr 2
      ring

end

end Submission.Obl.k4_finite_affine_candidate_return
