import Submission.Obl.k4_horizontal_wide_interval_return.ScalarCell
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

namespace Submission.Obl.k4_horizontal_wide_interval_return

open Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

namespace CellFrame

/-- The original whole-block geometry bounds all five normalized scalar
coefficients. This is independent of the ordinary sizes of the native affine
coefficients, which can have fixed-power cost. -/
theorem lineCoeffs_bound_of_geometry (F : CellFrame) (b : Fin 6 → ℝ)
    {K : ℝ} (hK : 1 ≤ K) (hq : F.q ≠ 0) (hg : F.g ≠ 0) (ha : F.a ≠ 0)
    (hC : ∀ i, |F.C i| ≤ K)
    (hgeom : ∀ z ∈ Icc (0 : ℝ) 1,
      |F.zZ (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))| ≤ K ∧
      |F.U (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))
        (lineY b (F.t₀ + F.q * z))| ≤ K ∧
      |F.resid (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))
        (lineY b (F.t₀ + F.q * z)) (lineX b (F.t₀ + F.q * z))| ≤ K) :
    ∀ i, |F.lineCoeffs b i| ≤ 40 * K ^ 3 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hK3 : K ^ 2 ≤ K ^ 3 := by
    have := mul_le_mul_of_nonneg_left hK (sq_nonneg K)
    nlinarith
  have hy (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      |F.lineCoeffs b 0 + z * F.lineCoeffs b 1| ≤ K := by
    rw [← lineCoeffs_y hq]
    exact (hgeom z hz).1
  have hy0 : |F.lineCoeffs b 0| ≤ K := by simpa using hy 0 (by norm_num)
  have hy1 : |F.lineCoeffs b 1| ≤ 2 * K := by
    have h := hy 1 (by norm_num)
    simp only [one_mul] at h
    rw [abs_le] at hy0 h ⊢
    constructor <;> linarith
  have hsig (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      |F.sig (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))
        (lineY b (F.t₀ + F.q * z)) (lineX b (F.t₀ + F.q * z))| ≤ 5 * K ^ 3 := by
    obtain ⟨hZ, hU, hR⟩ := hgeom z hz
    have hz1 : |z| ≤ 1 := by rw [abs_of_nonneg hz.1]; exact hz.2
    have hα : |F.C 0 + F.C 1 * F.zt (F.t₀ + F.q * z) +
        F.C 2 * F.zZ (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))| ≤ 2 * K + K ^ 2 := by
      rw [zt_line hq]
      calc _ ≤ |F.C 0| + |F.C 1 * z| +
          |F.C 2 * F.zZ (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ K + K * 1 + K * K := by simp only [abs_mul]; gcongr <;> exact hC _
        _ = 2 * K + K ^ 2 := by ring
    have hP : |F.Pnc (F.t₀ + F.q * z) (lineZ b (F.t₀ + F.q * z))
        (lineY b (F.t₀ + F.q * z))| ≤ (2 * K + K ^ 2) * K + K * K ^ 2 := by
      unfold Pnc
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul hα hU (abs_nonneg _) (by positivity)
      · rw [abs_mul, abs_pow]
        exact mul_le_mul (hC 3) (pow_le_pow_left₀ (abs_nonneg _) hU 2)
          (sq_nonneg _) hK0
    unfold sig
    exact (abs_sub _ _).trans ((add_le_add hR hP).trans (by nlinarith))
  let c : Fin 6 → ℝ := ![F.lineCoeffs b 2, F.lineCoeffs b 3, 0, F.lineCoeffs b 4, 0, 0]
  have hx : ∀ i, |c i| ≤ 8 * (5 * K ^ 3) := quadratic_coefficients_bound (by
    intro z hz w hw
    have h := hsig z hz
    simp only [lineZ, lineY, lineX] at h
    rw [lineCoeffs_x hq hg ha] at h
    simpa [c, quadraticValue, mul_comm] using h)
  have hx0 := hx 0
  have hx1 := hx 1
  have hx2 := hx 3
  norm_num [c, mul_assoc] at hx0 hx1 hx2
  intro i
  fin_cases i
  · exact hy0.trans (by nlinarith)
  · exact hy1.trans (by nlinarith)
  · exact hx0.trans_eq (by ring)
  · exact hx1.trans_eq (by ring)
  · exact hx2.trans_eq (by ring)

end CellFrame

end Submission.Obl.k4_horizontal_wide_interval_return
