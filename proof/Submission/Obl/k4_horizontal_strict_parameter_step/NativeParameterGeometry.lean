/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeParameterGeometry.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.ParameterCellCount

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

/-- At the true time midpoint, the static initial parameters lie in a tilted
rectangle of widths `K h` and `K² h²`, uniformly within a common velocity bin. -/
theorem static_parameters_true_strip (b : Fin 6 → ℝ) (c : Fin 5 → ℝ)
    {m v h g χ K : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hK : 1 ≤ K)
    (hm : |m| ≤ 1) (hc : |c 4| ≤ K) (hg : g ≤ K * h) (hχ : χ ≤ h ^ 2)
    (hvel : |b 3 - v| ≤ χ) (hdef : |b 4 + b 0| ≤ χ)
    (hfirst : |b 0 + m * b 3 - c 0 - m * c 1| ≤ K * h)
    (hsecond : |b 1 + m * b 4 - c 2 - m * c 3 - c 4 * (b 0 + m * b 3)| ≤ K * h * g) :
    |b 0 - (c 0 + m * (c 1 - v))| ≤ 2 * K * h ∧
      |b 1 - (m + c 4) * b 0 - (c 2 + m * c 3 + c 4 * m * v)| ≤ 4 * K ^ 2 * h ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hχ0 : 0 ≤ χ := (abs_nonneg _).trans hvel
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hmul (z : ℝ) (hz : |z| ≤ χ) : |m * z| ≤ χ := by
    rw [abs_mul]
    exact (mul_le_mul hm hz (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  constructor
  · calc
      _ = |(b 0 + m * b 3 - c 0 - m * c 1) - m * (b 3 - v)| := by congr 1; ring
      _ ≤ |b 0 + m * b 3 - c 0 - m * c 1| + |m * (b 3 - v)| := abs_sub _ _
      _ ≤ K * h + χ := add_le_add hfirst (hmul _ hvel)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hK hh.le]
  · have hlast : |c 4 * m * (b 3 - v)| ≤ K * χ := by
      rw [mul_assoc, abs_mul]
      exact mul_le_mul hc (hmul _ hvel) (abs_nonneg _) hK0
    calc
      _ = |(b 1 + m * b 4 - c 2 - m * c 3 - c 4 * (b 0 + m * b 3)) -
        m * (b 4 + b 0) + c 4 * m * (b 3 - v)| := by congr 1; ring
      _ ≤ (|b 1 + m * b 4 - c 2 - m * c 3 - c 4 * (b 0 + m * b 3)| +
          |m * (b 4 + b 0)|) + |c 4 * m * (b 3 - v)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * h * g + χ + K * χ := add_le_add (add_le_add hsecond (hmul _ hdef)) hlast
      _ ≤ K ^ 2 * h ^ 2 + h ^ 2 + K * h ^ 2 := by
        have hgh := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ K * h)
        have hχK := mul_le_mul_of_nonneg_left hχ hK0
        nlinarith
      _ ≤ _ := by
        have h1 : 1 ≤ K ^ 2 := by nlinarith
        have h2 : K ≤ K ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg h),
          mul_le_mul_of_nonneg_right h2 (sq_nonneg h)]

/-- Every actual parameter cell of a true label is charged by its midpoint
rectangle. The resulting `h³/D²` count is the original threshold budget. -/
theorem true_parameter_cell_count (c : Fin 5 → ℝ) {m v h g χ K D : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hK : 1 ≤ K) (hm : |m| ≤ 1)
    (hc : |c 4| ≤ K) (hg : g ≤ K * h) (hχ : χ ≤ h ^ 2)
    (hD : 0 < D) (hDh : D ≤ h ^ 2) (S : Finset (Fin 2 → ℤ))
    (hS : ∀ q ∈ S, ∃ b : Fin 6 → ℝ,
      parameterCode D ![b 0, b 1] = q ∧ |b 3 - v| ≤ χ ∧ |b 4 + b 0| ≤ χ ∧
      |b 0 + m * b 3 - c 0 - m * c 1| ≤ K * h ∧
      |b 1 + m * b 4 - c 2 - m * c 3 - c 4 * (b 0 + m * b 3)| ≤ K * h * g) :
    (S.card : ℝ) * D ^ 2 ≤ 128 * K ^ 3 * h ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hDA : D ≤ 2 * K * h := by
    have hh2 : h ^ 2 ≤ h := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hK hh.le]
  have htilt : |m + c 4| ≤ 1 + K := (abs_add_le _ _).trans (add_le_add hm hc)
  have hDB : (1 + |m + c 4|) * D ≤ 4 * K ^ 2 * h ^ 2 := by
    calc
      _ ≤ (2 + K) * h ^ 2 :=
        mul_le_mul (by linarith) hDh hD.le (by linarith)
      _ ≤ _ := by
        have : 2 + K ≤ 4 * K ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg h)]
  have hcount := parameter_cells_in_strip hD hDA hDB S (by
    intro q hq
    obtain ⟨b, hcode, hvel, hdef, hfirst, hsecond⟩ := hS q hq
    have hstrip := static_parameters_true_strip b c hh hh1 hK hm hc hg hχ hvel hdef hfirst hsecond
    exact ⟨![b 0, b 1], hcode, hstrip⟩)
  convert hcount using 1
  ring

end Submission.Obl.k4_horizontal_strict_parameter_step
