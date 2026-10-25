import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- Rebound the physical coefficients from the actual moving-strip norm.
The supplied physical coefficient ceiling plays no role in this estimate. -/
theorem moving_strip_coefficients (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) {H u v D : ℝ} (hH : 0 ≤ H) (hD : 0 < D)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + D * w] P| ≤ H) :
    ∀ e, |P.coeff e| ≤ 240 * H * (1 + (1 + |u| + |v|) / D) ^ 2 := by
  obtain ⟨c, hc⟩ := isQuad2_affine_second (isQuad2_eval P hP) u v D
  have hcform : ∀ t w, eval ![t, u + t * v + D * w] P = quadraticValue c t w := hc
  have hcbd : ∀ i, |c i| ≤ 8 * H := quadratic_coefficients_bound (by
    intro t ht w hw
    rw [← hcform]
    exact hbound t ht w hw)
  let R := 1 + (1 + |u| + |v|) / D
  have hsum : 0 ≤ (1 + |u| + |v|) / D := by positivity
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hco (t z : ℝ) : eval ![t, z] P =
      quadraticValue (undoQuadraticFrame c u v D) t z := by
    have heq : u + t * v + D * ((z - u - t * v) / D) = z := by
      field_simp
      ring
    calc
      _ = eval ![t, u + t * v + D * ((z - u - t * v) / D)] P := by rw [heq]
      _ = quadraticValue c t ((z - u - t * v) / D) := hc _ _
      _ = _ := undoQuadraticFrame_value c u v hD.ne' t z
  have hu : |u / D| ≤ R := by
    rw [abs_div, abs_of_pos hD]
    calc
      _ ≤ (1 + |u| + |v|) / D := by gcongr; linarith [abs_nonneg v]
      _ ≤ R := by dsimp [R]; linarith
  have hv : |v / D| ≤ R := by
    rw [abs_div, abs_of_pos hD]
    calc
      _ ≤ (1 + |u| + |v|) / D := by gcongr; linarith [abs_nonneg u]
      _ ≤ R := by dsimp [R]; linarith
  have hDi : |D⁻¹| ≤ R := by
    rw [abs_of_pos (inv_pos.mpr hD), ← one_div]
    calc
      _ ≤ (1 + |u| + |v|) / D := by
        gcongr
        linarith [abs_nonneg u, abs_nonneg v]
      _ ≤ R := by dsimp [R]; linarith
  have hphys (i : Fin 6) : |undoQuadraticFrame c u v D i| ≤ 40 * H * R ^ 2 := by
    convert undoQuadraticFrame_bound (by positivity : 0 ≤ 8 * H) hR hcbd hu hv hDi i using 1
    ring
  rw [polynomial_eq_of_quadratic_values hco]
  intro e
  convert quadraticPolynomial_coeff_bound (by positivity : 0 ≤ 40 * H * R ^ 2) hphys e using 1
  dsimp [R]
  ring

/-- The moving norm costs twice the physical width exponent; the other
costs can be arbitrarily small. -/
theorem moving_strip_coefficients_power {N B η u v : ℝ}
    (hN : 1 ≤ N) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (hcenter : |u| + |v| ≤ N ^ η)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + N ^ (-B) * w] P| ≤ N ^ η) :
    ∀ e, |P.coeff e| ≤ 2160 * N ^ (2 * B + 3 * η) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hE : 1 ≤ N ^ η := Real.one_le_rpow hN hη
  have hF : 1 ≤ N ^ B := Real.one_le_rpow hN hB
  have hquot : 1 + (1 + |u| + |v|) / N ^ (-B) ≤ 3 * N ^ (B + η) := by
    rw [Real.rpow_neg hNp.le, div_inv_eq_mul]
    calc
      _ ≤ 1 + (1 + N ^ η) * N ^ B := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (by linarith : 1 + |u| + |v| ≤ 1 + N ^ η) (by positivity))
      _ ≤ 3 * (N ^ B * N ^ η) := by nlinarith [mul_le_mul hF hE (by norm_num) (by positivity)]
      _ = _ := by rw [Real.rpow_add hNp]
  intro e
  calc
    _ ≤ 240 * N ^ η * (1 + (1 + |u| + |v|) / N ^ (-B)) ^ 2 :=
      moving_strip_coefficients P hP (by positivity) (by positivity) hbound e
    _ ≤ 240 * N ^ η * (3 * N ^ (B + η)) ^ 2 := by gcongr
    _ = 2160 * (N ^ η * (N ^ (B + η) * N ^ (B + η))) := by ring
    _ = 2160 * N ^ (2 * B + 3 * η) := by
      rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]
      congr 2
      ring

/-- The physical coefficient budget is fixed before the final loss, and
has no constant exponent increment. This is uniform over all predictors. -/
theorem eventually_moving_strip_coefficients {N : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ (P : MvPolynomial (Fin 2) ℝ) (u v : ℝ),
      P.totalDegree ≤ 2 → |u| + |v| ≤ N k ^ (ε / 6) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
        |eval ![t, u + t * v + N k ^ (-B) * w] P| ≤ N k ^ (ε / 6)) →
      ∀ e, |P.coeff e| ≤ N k ^ (2 * B + ε) := by
  have hnum := hNt.eventually (eventually_const_mul_rpow_le 2160
    (show 2 * B + 3 * (ε / 6) < 2 * B + ε by linarith))
  filter_upwards [hnum] with k hk P u v hP hcenter hbound e
  exact (moving_strip_coefficients_power (hN k) hB (by positivity)
    P hP hcenter hbound e).trans hk

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
