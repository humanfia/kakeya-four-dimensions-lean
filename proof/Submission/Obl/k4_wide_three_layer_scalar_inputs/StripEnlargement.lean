import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- A quadratic's norm on an enlarged moving strip costs only the square
of the enlargement, independently of its physical coefficient size. -/
theorem moving_strip_enlargement (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) {H u v D L : ℝ} (hH : 0 ≤ H) (hD : 0 < D)
    (hL : 1 ≤ L)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + D * w] P| ≤ H)
    {t Y : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hY : |Y - u - t * v| ≤ L * D) :
    |eval ![t, Y] P| ≤ 48 * H * L ^ 2 := by
  obtain ⟨c, hc⟩ := isQuad2_affine_second (isQuad2_eval P hP) u v D
  have hcform : ∀ t w, eval ![t, u + t * v + D * w] P = quadraticValue c t w := hc
  have hcbd : ∀ i, |c i| ≤ 8 * H := quadratic_coefficients_bound (by
    intro τ hτ w hw
    rw [← hcform]
    exact hbound τ hτ w hw)
  have hw : |(Y - u - t * v) / D| ≤ L := by
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    exact hY
  have heq : u + t * v + D * ((Y - u - t * v) / D) = Y := by
    field_simp
    ring
  have h := quadraticValue_bound (H := 8 * H) (by positivity) hL hcbd
    (t := t) (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]) hw
  rw [← hcform, heq] at h
  convert h using 1 <;> ring

/-- The enlarged strip can be used as the new comparison frame while
all reference weights remain those of the original strip. -/
theorem moving_strip_enlarged_norm (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) {H u v D L : ℝ} (hH : 0 ≤ H) (hD : 0 < D)
    (hL : 1 ≤ L)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + D * w] P| ≤ H) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + (L * D) * w] P| ≤ 48 * H * L ^ 2 := by
  intro t ht w hw
  apply moving_strip_enlargement P hP hH hD hL hbound ht
  have hw' : |w| ≤ 1 := abs_le.mpr hw
  have hL0 : 0 ≤ L := by linarith
  calc |u + t * v + L * D * w - u - t * v| = L * D * |w| := by
        rw [show u + t * v + L * D * w - u - t * v = L * D * w by ring,
          abs_mul, abs_of_nonneg (mul_nonneg hL0 hD.le)]
    _ ≤ L * D := by simpa using mul_le_mul_of_nonneg_left hw' (mul_nonneg hL0 hD.le)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
