/- Adapted from our LOT tree o211, session x0736, commit fb9fb2638e83e4e42cdf985859ec4b5deb228222,
`Submission/Obl/k4_critical_affine_derivative_preparation/NativePrimitive.lean`.
Earlier provenance comments in that file are retained below. -/

import Mathlib

/-! Adapted from our LOT tree o107, session x0353, AffinePrimitive.lean
(commit 2d33b59a). Only the derivative primitive is needed here. -/

namespace Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

def primitiveCoefficients (B : Fin 2 → ℝ) (lam H t₀ Z₀ : ℝ) : Fin 4 → ℝ :=
  ![0, B 0 + lam * Z₀ / H, B 1 - lam * t₀ / H, lam / H]

def affineResidualIntercept (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) : ℝ :=
  b 2 - A 0 - A 2 * b 0 - A 3 * b 1

def affineResidualSlope (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) : ℝ :=
  b 5 - A 1 - A 2 * b 3 - A 3 * b 4

/-- The skew row-fit output has an affine primitive along native trajectories.
The remaining error is bounded by the row errors and the horizontal defect. -/
theorem row_fit_primitive_slope_bound
    (b : Fin 6 → ℝ) (T B : Fin 2 → ℝ) (lam H t₀ Z₀ t K L E F ε : ℝ)
    (hH : 0 < H) (hv : |b 3| ≤ K) (hlam : |lam| ≤ L)
    (hdefect : |b 4 + b 0| ≤ ε)
    (hlinear : |b 5 - T 0 - b 3 * T 1| ≤ E)
    (hrow0 : |T 0 - B 0 + lam * ((b 0 + t * b 3 - Z₀) / H)| ≤ F)
    (hrow1 : |T 1 - B 1 - lam * ((t - t₀) / H)| ≤ F) :
    |affineResidualSlope (primitiveCoefficients B lam H t₀ Z₀) b| ≤
      E + (1 + K) * F + L * ε / H := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hv
  have hL : 0 ≤ L := (abs_nonneg _).trans hlam
  have hF : 0 ≤ F := (abs_nonneg _).trans hrow0
  have hε : 0 ≤ ε := (abs_nonneg _).trans hdefect
  have hm : |b 3 * (T 1 - B 1 - lam * ((t - t₀) / H))| ≤ K * F := by
    rw [abs_mul]
    exact mul_le_mul hv hrow1 (abs_nonneg _) hK
  have hd : |(lam / H) * (b 4 + b 0)| ≤ L * ε / H := by
    calc
      _ = (|lam| / H) * |b 4 + b 0| := by rw [abs_mul, abs_div, abs_of_pos hH]
      _ ≤ (L / H) * ε :=
        mul_le_mul (div_le_div_of_nonneg_right hlam hH.le) hdefect (abs_nonneg _)
          (div_nonneg hL hH.le)
      _ = _ := by ring
  have hsum : |(b 5 - T 0 - b 3 * T 1) +
      (T 0 - B 0 + lam * ((b 0 + t * b 3 - Z₀) / H)) +
      b 3 * (T 1 - B 1 - lam * ((t - t₀) / H))| ≤ E + F + K * F :=
    (abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add hlinear hrow0)) hm)
  have heq : affineResidualSlope (primitiveCoefficients B lam H t₀ Z₀) b =
      ((b 5 - T 0 - b 3 * T 1) +
        (T 0 - B 0 + lam * ((b 0 + t * b 3 - Z₀) / H)) +
        b 3 * (T 1 - B 1 - lam * ((t - t₀) / H))) - (lam / H) * (b 4 + b 0) := by
    simp [affineResidualSlope, primitiveCoefficients]
    ring
  rw [heq]
  exact (abs_sub _ _).trans ((add_le_add hsum hd).trans_eq (by ring))

/-- Conversion from the normalized skew row to physical affine slopes costs
only the reciprocal of the true time length. -/
theorem primitiveCoefficients_bound
    (B : Fin 2 → ℝ) (lam H t₀ Z₀ K C : ℝ)
    (hH : 0 < H) (hHone : H ≤ 1) (hK : 0 ≤ K)
    (ht₀ : |t₀| ≤ K) (hZ₀ : |Z₀| ≤ K)
    (hB : |B 0| + |B 1| + |lam| ≤ C) :
    ∀ e : Fin 3, |primitiveCoefficients B lam H t₀ Z₀ e.succ| ≤ (1 + K) * C / H := by
  have hC : 0 ≤ C := by linarith [abs_nonneg (B 0), abs_nonneg (B 1), abs_nonneg lam]
  have hB₀ : |B 0| ≤ C := by linarith [abs_nonneg (B 1), abs_nonneg lam]
  have hB₁ : |B 1| ≤ C := by linarith [abs_nonneg (B 0), abs_nonneg lam]
  have hlam : |lam| ≤ C := by linarith [abs_nonneg (B 0), abs_nonneg (B 1)]
  have hbase (x : ℝ) (hx : |x| ≤ C) (y : ℝ) (hy : |y| ≤ K) :
      |x + lam * y / H| ≤ (1 + K) * C / H := by
    apply (abs_add_le _ _).trans
    rw [abs_div, abs_mul, abs_of_pos hH]
    apply (le_div_iff₀ hH).mpr
    have hmul := mul_le_mul hlam hy (abs_nonneg y) hC
    have hnum : |x| * H ≤ C :=
      (mul_le_mul_of_nonneg_left hHone (abs_nonneg x)).trans (by simpa using hx)
    calc
      (|x| + |lam| * |y| / H) * H = |x| * H + |lam| * |y| := by field_simp
      _ ≤ C + C * K := add_le_add hnum hmul
      _ = (1 + K) * C := by ring
  intro e
  fin_cases e
  · exact hbase (B 0) hB₀ Z₀ hZ₀
  · change |B 1 - lam * t₀ / H| ≤ (1 + K) * C / H
    simpa only [mul_neg, neg_div, sub_eq_add_neg] using hbase (B 1) hB₁ (-t₀) (by simpa using ht₀)
  · change |lam / H| ≤ (1 + K) * C / H
    rw [abs_div, abs_of_pos hH]
    apply div_le_div_of_nonneg_right _ hH.le
    exact hlam.trans (by nlinarith only [mul_nonneg hK hC])

/-- The trajectory-position convention used by Row agrees with physical
coordinates after the actual time and horizontal translation. -/
theorem normalized_native_position
    (b : Fin 6 → ℝ) (H t₀ Z₀ τ : ℝ) (hH : H ≠ 0) :
    (b 0 + t₀ * b 3 - Z₀) / H + τ * b 3 =
      (b 0 + (t₀ + H * τ) * b 3 - Z₀) / H := by
  field_simp
  ring

/-- A normalized Row event implies the desired constant trajectory-derivative
fit. No differentiation of a restricted time set is involved. -/
theorem normalized_row_fit_primitive_slope_bound
    (b : Fin 6 → ℝ) (T B : Fin 2 → ℝ) (lam H t₀ Z₀ τ K C E F ε : ℝ)
    (hH : 0 < H) (hv : |b 3| ≤ K) (hlam : |lam| ≤ C)
    (hdefect : |b 4 + b 0| ≤ ε)
    (hlinear : |b 5 - T 0 - b 3 * T 1| ≤ E)
    (hrow0 : |T 0 - B 0 + lam * ((b 0 + t₀ * b 3 - Z₀) / H + τ * b 3)| ≤ F)
    (hrow1 : |T 1 - B 1 - lam * τ| ≤ F) :
    |affineResidualSlope (primitiveCoefficients B lam H t₀ Z₀) b| ≤
      E + (1 + K) * F + C * ε / H := by
  apply row_fit_primitive_slope_bound b T B lam H t₀ Z₀ (t₀ + H * τ) K C E F ε
    hH hv hlam hdefect hlinear
  · simpa only [normalized_native_position b H t₀ Z₀ τ hH.ne'] using hrow0
  · have ht : (t₀ + H * τ - t₀) / H = τ := by field_simp [hH.ne']; ring
    simpa only [ht] using hrow1

end

end Submission.Obl.k4_critical_conditional_row_preparation
