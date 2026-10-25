import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.KeyFullPolynomial
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.FullResidualChartReplacement
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

namespace Support.Frame

/-- The same physical frame, with an unused zero transverse correction. -/
def cellFrame (F : Support.Frame) : CellFrame :=
  ⟨F.t₀, F.q, F.g, F.a, F.c, F.L, 0⟩

theorem cellFrame_U (F : Support.Frame) (b : Fin 6 → ℝ) (t : ℝ) :
    F.cellFrame.U t (b 0 + t * b 3) (b 1 + t * b 4) = F.tr b t := rfl

theorem cellFrame_resid (F : Support.Frame) (b : Fin 6 → ℝ) (t : ℝ) :
    F.cellFrame.resid t (b 0 + t * b 3) (b 1 + t * b 4) (b 2 + t * b 5) =
      F.resid b t := rfl

end Support.Frame

namespace KeyFrame

/-- The chart polynomial's time-only part, in the full normalized base convention. -/
def baseCoefficients (p : Fin 6 → ℝ) : Fin 6 → ℝ := ![p 0, p 1, 0, p 3, 0, 0]

/-- Its transverse part. The chart has no normalized horizontal-position coefficient. -/
def transverseCoefficients (p : Fin 6 → ℝ) : Fin 4 → ℝ := ![p 2, p 4, 0, p 5]

theorem prediction_split (p : Fin 6 → ℝ) (τ z U : ℝ) :
    quadraticValue p τ U = Support.quadZ (baseCoefficients p) τ z +
      Support.transv (transverseCoefficients p) τ z U := by
  simp [quadraticValue, Support.quadZ, Support.transv, baseCoefficients,
    transverseCoefficients]
  ring

theorem prediction_coefficients_bound {p : Fin 6 → ℝ} {H : ℝ}
    (hH : 0 ≤ H) (hp : ∀ i, |p i| ≤ H) :
    (∀ i, |baseCoefficients p i| ≤ H) ∧
      (∀ i, |transverseCoefficients p i| ≤ H) := by
  constructor
  · intro i
    fin_cases i <;> simp [baseCoefficients, hp, hH]
  · intro i
    fin_cases i <;> simp [transverseCoefficients, hp, hH]

theorem chart_prediction_coefficients_bound (F : CellFrame) {Zk Vk Yk H B : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hβ : |chartBeta F Zk Vk Yk 0| + |chartBeta F Zk Vk Yk 1| ≤ B)
    (r : Fin 6 → ℝ) (hr : ∀ i, |r i| ≤ H) :
    (∀ i, |baseCoefficients (chartPolynomial F Zk Vk Yk r) i| ≤
      48 * H * (B + 1) ^ 2) ∧
    (∀ i, |transverseCoefficients (chartPolynomial F Zk Vk Yk r) i| ≤
      48 * H * (B + 1) ^ 2) :=
  prediction_coefficients_bound (by positivity) (chartPolynomial_bound F hH hB hβ r hr)

/-- Freezing the physical residual preserves the actual transverse coordinate exactly. -/
theorem chart_shift_preserves_U (F : CellFrame) (t Z Z' Y : ℝ) :
    F.U t Z' (Y - F.c 4 * (Z - Z')) = F.U t Z Y := by
  unfold CellFrame.U
  congr 1
  ring

/-- The chart polynomial can be evaluated at the actual point's normalized transverse
coordinate. Only the physical residual's chart replacement incurs an error. -/
theorem chart_prediction_error (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (G : MvPolynomial (Fin 2) ℝ) (r : Fin 6 → ℝ) (Zk Vk Yk : ℝ)
    (hkey : ∀ τ y : ℝ,
      (eval ![F.t₀ + F.q * τ, keyY (F.q * F.g) F.q Yk Zk τ y] G -
        F.fit (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))
          (keyY (F.q * F.g) F.q Yk Zk τ y)) / F.a = quadraticValue r τ y)
    (t Z Y z E : ℝ)
    (herror : |physicalResidual G F.L F.a t Z Y -
      physicalResidual G F.L F.a t (keyZ Zk Vk t)
        (Y - F.c 4 * (Z - keyZ Zk Vk t))| ≤ E) :
    |F.resid t Z Y (eval ![t, Y] G) -
      Support.quadZ (baseCoefficients (chartPolynomial F Zk Vk Yk r)) (F.zt t) z -
      Support.transv (transverseCoefficients (chartPolynomial F Zk Vk Yk r))
        (F.zt t) z (F.U t Z Y)| ≤ E := by
  have ht : F.t₀ + F.q * F.zt t = t := by
    unfold CellFrame.zt
    field_simp
    ring
  have hY : baseY F t (keyZ Zk Vk t) + F.q * F.g * F.U t Z Y =
      Y - F.c 4 * (Z - keyZ Zk Vk t) := by
    unfold baseY CellFrame.U
    field_simp
    ring
  have hchart := chartPolynomial_residual F hq hg G r Zk Vk Yk hkey (F.zt t) (F.U t Z Y)
  dsimp only at hchart
  rw [ht, hY, prediction_split (z := z)] at hchart
  have hchart' : physicalResidual G F.L F.a t (keyZ Zk Vk t)
      (Y - F.c 4 * (Z - keyZ Zk Vk t)) =
      Support.quadZ (baseCoefficients (chartPolynomial F Zk Vk Yk r)) (F.zt t) z +
      Support.transv (transverseCoefficients (chartPolynomial F Zk Vk Yk r))
        (F.zt t) z (F.U t Z Y) := hchart
  rw [hchart'] at herror
  convert herror using 1
  congr 1
  change (eval ![t, Y] G - F.fit t Z Y) / F.a - _ - _ = _
  simp only [physicalResidual, CellFrame.fit]
  ring

/-- The entire `ComparedBlock` fit follows by adding the original projected fit, the
whole-domain frozen offset error, and the physical chart error, in their original units. -/
theorem residual_fit_of_chart_prediction (F : CellFrame) (ha : 0 < F.a)
    (G : MvPolynomial (Fin 2) ℝ) (p : Fin 6 → ℝ)
    {t Z Y X z D E W Echart : ℝ}
    (hfit : |X - eval ![t, Y] G - F.a * D| ≤ E + W)
    (hchart : |F.resid t Z Y (eval ![t, Y] G) -
      Support.quadZ (baseCoefficients p) (F.zt t) z -
      Support.transv (transverseCoefficients p) (F.zt t) z (F.U t Z Y)| ≤ Echart) :
    |F.resid t Z Y X - Support.quadZ (baseCoefficients p) (F.zt t) z - D -
      Support.transv (transverseCoefficients p) (F.zt t) z (F.U t Z Y)| ≤
      (E + W) / F.a + Echart := by
  have hid : F.resid t Z Y X - Support.quadZ (baseCoefficients p) (F.zt t) z - D -
      Support.transv (transverseCoefficients p) (F.zt t) z (F.U t Z Y) =
      (X - eval ![t, Y] G - F.a * D) / F.a +
      (F.resid t Z Y (eval ![t, Y] G) -
        Support.quadZ (baseCoefficients p) (F.zt t) z -
        Support.transv (transverseCoefficients p) (F.zt t) z (F.U t Z Y)) := by
    unfold CellFrame.resid
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ |(X - eval ![t, Y] G - F.a * D) / F.a| +
        |F.resid t Z Y (eval ![t, Y] G) -
          Support.quadZ (baseCoefficients p) (F.zt t) z -
          Support.transv (transverseCoefficients p) (F.zt t) z (F.U t Z Y)| := abs_add_le _ _
    _ ≤ (E + W) / F.a + Echart := by
      apply add_le_add _ hchart
      rw [abs_div, abs_of_pos ha]
      exact div_le_div_of_nonneg_right hfit ha.le

end KeyFrame

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
