-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.CapExponentNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/CapExponentNumerics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/CapExponentNumerics.lean.
All earlier source attributions below are retained. -/
import Mathlib

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open scoped ENNReal

/-- The original density ceiling, divided by the old packet budget,
has the expected profile-increment exponent. -/
theorem pure_cap_coefficient {N κ K fOld fNew d₁ step error τ ε : ℝ}
    (hN : 1 ≤ N) (hκ : 0 ≤ κ)
    (hprofile : fOld - fNew ≤ -d₁ * step + error) :
    ((ENNReal.ofReal (N ^ (-fNew + τ + ε)) *
        ENNReal.ofReal (64 * (max κ K) ^ 2)) *
        ENNReal.ofReal (κ * N ^ fOld)) ≤
      ENNReal.ofReal (64 * (max κ K) ^ 2 * κ *
        N ^ (-d₁ * step + error + τ + ε)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  calc
    _ = ENNReal.ofReal
        ((N ^ (-fNew + τ + ε) * (64 * (max κ K) ^ 2)) * (κ * N ^ fOld)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ N ^ (-fNew + τ + ε) *
        (64 * (max κ K) ^ 2)), ENNReal.ofReal_mul (Real.rpow_nonneg hNp.le _)]
    _ = ENNReal.ofReal (64 * (max κ K) ^ 2 * κ *
        N ^ (fOld - fNew + τ + ε)) := by
      congr 1
      have hpow : N ^ (fOld - fNew + τ + ε) =
          N ^ (-fNew + τ + ε) * N ^ fOld := by
        calc
          _ = N ^ ((-fNew + τ + ε) + fOld) := by congr 1; ring
          _ = _ := Real.rpow_add hNp _ _
      rw [hpow]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity))

/-- Both endpoint errors of the frozen affine profile pay for this cap. -/
theorem profile_increment_for_cap {f : ℝ → ℝ} {f₀ d₁ r r' error : ℝ}
    (h : |f r - f₀ - d₁ * r| ≤ error)
    (h' : |f r' - f₀ - d₁ * r'| ≤ error) :
    f r - f r' ≤ -d₁ * (r' - r) + 2 * error := by
  have hlo := (abs_le.mp h').1
  have hhi := (abs_le.mp h).2
  nlinarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
