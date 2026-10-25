-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate

/-- All scale factors in the affine change of variables, with the exponent `K` unchanged. -/
theorem scaled_power_identity {κ θ δ lam m : ℝ}
    (hκ : 0 < κ) (hθ : 0 < θ) (hδ : 0 < δ) (hlam : 0 < lam) (hm : 0 < m)
    (a K α N : ℝ) :
    (κ ^ 3 * (θ⁻¹) ^ 2) *
      ((a * κ ^ ((3 / 2 : ℝ) + α) * κ ^ K * (κ⁻¹) ^ (-K) / κ ^ 3) *
        δ ^ ((3 / 2 : ℝ) + α) * θ ^ ((1 / 2 : ℝ) - α) * lam ^ K * m ^ (-K) * N) =
      a * (κ * θ⁻¹ * δ) ^ ((3 / 2 : ℝ) + α) * (κ * lam) ^ K *
        (m / κ) ^ (-K) * N := by
  have ht : (θ⁻¹) ^ 2 * θ ^ ((1 / 2 : ℝ) - α) = (θ⁻¹) ^ ((3 / 2 : ℝ) + α) := by
    rw [← Real.rpow_natCast (θ⁻¹) 2, Real.inv_rpow hθ.le, ← Real.rpow_neg hθ.le,
      ← Real.rpow_add hθ, Real.inv_rpow hθ.le, ← Real.rpow_neg hθ.le]
    congr 1
    norm_num
    ring
  rw [Real.mul_rpow (mul_nonneg hκ.le (inv_nonneg.mpr hθ.le)) hδ.le,
    Real.mul_rpow hκ.le (inv_nonneg.mpr hθ.le), Real.mul_rpow hκ.le hlam.le,
    div_eq_mul_inv m κ, Real.mul_rpow hm.le (inv_nonneg.mpr hκ.le)]
  calc
    _ = (a * κ ^ ((3 / 2 : ℝ) + α) * κ ^ K * (κ⁻¹) ^ (-K)) *
        δ ^ ((3 / 2 : ℝ) + α) *
        ((θ⁻¹) ^ 2 * θ ^ ((1 / 2 : ℝ) - α)) * lam ^ K * m ^ (-K) * N := by
      field_simp
    _ = _ := by rw [ht]; ring

end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
