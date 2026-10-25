-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/Extrapolation.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 3be7d21a,
-- Submission/Obl/k4_terminal_time_extension/Extrapolation.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.Interface
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.QuadBounds
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

/-!
# Polynomial extrapolation of chart tests along trajectories

A test of total degree at most two restricted to a trajectory is a quadratic in
time.  A bound `M` on an interval of length `h` therefore extends to every time
`t`, with the loss `3 ((|t - s| + h) / (h / 2))²` of the three-point bound of
accepted o094 (`quad_three_point_bound`).  On a longer block of length `ℓ`
containing an old block of length `2^-T₀`, the old chart's value and hidden
derivative bounds `κ δ`, `κ B` become `12 κ δ (ℓ 2^T₀ + 1)²` and
`12 κ B (ℓ 2^T₀ + 1)²` (paper display `a02:old-test-extrapolation`).
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MvPolynomial Set

/-- A test of total degree at most two is a quadratic in time along a trajectory. -/
theorem eval_x_quadratic (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l : ℕ × (Fin 6 → ℝ)) :
    ∃ a b c : ℝ, ∀ t, eval (x l t) R = a + b * t + c * t ^ 2 := by
  set p : Polynomial ℝ := MvPolynomial.eval₂ Polynomial.C
    ![Polynomial.X, Polynomial.C (l.2 0) + Polynomial.C (l.2 3) * Polynomial.X,
      Polynomial.C (l.2 1) + Polynomial.C (l.2 4) * Polynomial.X,
      Polynomial.C (l.2 2) + Polynomial.C (l.2 5) * Polynomial.X] R with hp
  have hdeg : p.natDegree ≤ 2 := by
    refine (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le R _ ?_).trans hR
    have h1 (u w : ℝ) : (Polynomial.C u + Polynomial.C w * Polynomial.X).natDegree ≤ 1 := by
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · simp
      · exact (Polynomial.natDegree_C_mul_le w Polynomial.X).trans (by simp)
    intro i
    fin_cases i
    · simp
    · exact h1 _ _
    · exact h1 _ _
    · exact h1 _ _
  obtain ⟨a, b, c, hq⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hdeg
  refine ⟨c, b, a, fun t => ?_⟩
  have hev : p.eval t = eval (x l t) R := by
    rw [hp, Submission.Obl.k4_quadratic_slope_volume.eval_polynomial_substitution]
    have hv : (fun i => (![Polynomial.X, Polynomial.C (l.2 0) + Polynomial.C (l.2 3) * Polynomial.X,
        Polynomial.C (l.2 1) + Polynomial.C (l.2 4) * Polynomial.X,
        Polynomial.C (l.2 2) + Polynomial.C (l.2 5) * Polynomial.X] i).eval t) = x l t := by
      funext i
      fin_cases i <;> simp [x] <;> ring
    rw [hv]
  rw [← hev, hq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  ring

/-- Extrapolation of a degree-two test along a trajectory from an interval of
length `h` to any time. -/
theorem test_extrapolate (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l : ℕ × (Fin 6 → ℝ)) {s h M : ℝ} (hh : 0 < h)
    (hM : ∀ t ∈ Icc s (s + h), |eval (x l t) R| ≤ M) (t : ℝ) :
    |eval (x l t) R| ≤ 3 * M * ((|t - s| + h) / (h / 2)) ^ 2 := by
  obtain ⟨a, b, c, hq⟩ := eval_x_quadratic R hR l
  have h₁ := hM s ⟨le_rfl, by linarith⟩
  have h₂ := hM (s + h / 2) ⟨by linarith, by linarith⟩
  have h₃ := hM (s + h) ⟨by linarith, le_rfl⟩
  rw [hq] at h₁ h₂ h₃
  rw [hq]
  have := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.quad_three_point_bound
    (a := a) (b := b) (c := c) (A := M) (δ := h / 2) (x₁ := s) (x₂ := s + h / 2) (x₃ := s + h)
    (by linarith) (by linarith) (by linarith) h₁ h₂ h₃ t
  calc |a + b * t + c * t ^ 2| ≤ 3 * M * ((|t - s| + (s + h - s)) / (h / 2)) ^ 2 := this
    _ = 3 * M * ((|t - s| + h) / (h / 2)) ^ 2 := by ring_nf

/-- On a block of length `ℓ` containing the old block `[j₀/2^T₀, (j₀+1)/2^T₀]`, a test
bounded by `M` on the old block is bounded by `12 M (ℓ 2^T₀ + 1)²`. -/
theorem test_extrapolate_block (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    (l : ℕ × (Fin 6 → ℝ)) {j₀ a ℓ M : ℝ} {T₀ : ℕ}
    (hM : ∀ t ∈ Icc (j₀ / (2 : ℝ) ^ T₀) ((j₀ + 1) / (2 : ℝ) ^ T₀), |eval (x l t) R| ≤ M)
    (ha : a ≤ j₀ / (2 : ℝ) ^ T₀) (hb : (j₀ + 1) / (2 : ℝ) ^ T₀ ≤ a + ℓ)
    {t : ℝ} (ht : t ∈ Icc a (a + ℓ)) :
    |eval (x l t) R| ≤ 12 * M * (ℓ * (2 : ℝ) ^ T₀ + 1) ^ 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  set h : ℝ := ((2 : ℝ) ^ T₀)⁻¹ with hhdef
  have hh : 0 < h := inv_pos.mpr hpos
  set s : ℝ := j₀ / (2 : ℝ) ^ T₀ with hs
  have hsh : s + h = (j₀ + 1) / (2 : ℝ) ^ T₀ := by
    rw [hs, hhdef]; field_simp
  have hM' : ∀ t ∈ Icc s (s + h), |eval (x l t) R| ≤ M := by
    intro t ht; rw [hsh] at ht; exact hM t ht
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM' s ⟨le_rfl, by linarith⟩)
  have hbound := test_extrapolate R hR l hh hM' t
  have hdist : |t - s| ≤ ℓ := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hℓ0 : 0 ≤ ℓ := le_trans (abs_nonneg _) hdist
  calc |eval (x l t) R| ≤ 3 * M * ((|t - s| + h) / (h / 2)) ^ 2 := hbound
    _ ≤ 3 * M * ((ℓ + h) / (h / 2)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 12 * M * (ℓ * (2 : ℝ) ^ T₀ + 1) ^ 2 := by
        rw [hhdef]
        field_simp
        ring

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
