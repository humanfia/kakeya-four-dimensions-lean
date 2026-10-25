import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.Prediction
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.KeyTransverseExpansion
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Keys

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open Inherited.Native

noncomputable section

namespace KeyFrame

/-- The discrepancy is computed from the actual recovered native key coefficients. -/
def nativeDiscrepancy (F : CellFrame) (Q : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 2) ℝ) (χ : ℝ) (key : Fin 3 → ℤ) : Fin 6 → ℝ :=
  sheetKeyCoeff G F.a χ (F.q * F.g) F.q F.t₀ key -
    blockKeyCoeff Q F.a χ (F.q * F.g) F.q F.t₀ key

/-- The defining recovered-key evaluation identity needs no analytic assumption. -/
theorem native_key_identity (F : CellFrame) (Q : MvPolynomial (Fin 4) ℝ)
    (hQ : Inherited.Native.HorizontalForm Q F.L)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (χ : ℝ) (key : Fin 3 → ℤ) :
    ∀ τ y : ℝ,
      (eval ![F.t₀ + F.q * τ,
          keyY (F.q * F.g) F.q ((key 2 : ℝ) * (F.q * F.g)) ((key 1 : ℝ) * χ) τ y] G -
        F.fit (F.t₀ + F.q * τ)
          (keyZ ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ) (F.t₀ + F.q * τ))
          (keyY (F.q * F.g) F.q ((key 2 : ℝ) * (F.q * F.g)) ((key 1 : ℝ) * χ) τ y)) /
        F.a = quadraticValue (nativeDiscrepancy F Q G χ key) τ y := by
  apply discrepancy_key_identity
  · intro τ y
    rw [← Inherited.CompareSheets.quad2_eq, quad2_sheetKeyCoeff hG]
    rfl
  · intro τ y
    rw [← Inherited.CompareSheets.quad2_eq, quad2_blockKeyCoeff hQ, blockGraph_eq hQ]
    rfl

/-- The whole chart prediction associated to the original coarse sheet and short key. -/
def nativeChartPolynomial (F : CellFrame) (Q : MvPolynomial (Fin 4) ℝ)
    (G : MvPolynomial (Fin 2) ℝ) (χ : ℝ) (key : Fin 3 → ℤ) : Fin 6 → ℝ :=
  chartPolynomial F ((key 1 : ℝ) * χ) ((key 0 : ℝ) * χ)
    ((key 2 : ℝ) * (F.q * F.g)) (nativeDiscrepancy F Q G χ key)

/-- Actual physical residuals are predicted in the exact `ComparedBlock` convention. -/
theorem native_prediction_error (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Inherited.Native.HorizontalForm Q F.L)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (χ : ℝ) (key : Fin 3 → ℤ) (t Z Y z E : ℝ)
    (herror : |physicalResidual G F.L F.a t Z Y -
      physicalResidual G F.L F.a t (domZ χ key t)
        (Y - F.c 4 * (Z - domZ χ key t))| ≤ E) :
    |F.resid t Z Y (eval ![t, Y] G) -
      Support.quadZ (baseCoefficients (nativeChartPolynomial F Q G χ key)) (F.zt t) z -
      Support.transv (transverseCoefficients (nativeChartPolynomial F Q G χ key))
        (F.zt t) z (F.U t Z Y)| ≤ E :=
  chart_prediction_error F hq hg G _ _ _ _ (native_key_identity F Q hQ G hG χ key)
    t Z Y z E herror

/-- The fixed physical coefficient horizon pays the complete native chart error uniformly
over all original keys, centers, discrepancy coefficients and arbitrarily small losses. -/
theorem eventually_native_prediction_error (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {s₀ sp M : ℝ}
    (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2) (hM : 100 * s₀ < M) :
    ∀ᶠ k in atTop, ∀ η : ℝ, 0 ≤ η → η ≤ s₀ →
      ∀ F : CellFrame, F.q ≠ 0 → F.g ≠ 0 → F.a = N k ^ (-sp) →
      ∀ Q : MvPolynomial (Fin 4) ℝ, Inherited.Native.HorizontalForm Q F.L →
      ∀ G : MvPolynomial (Fin 2) ℝ, G.totalDegree ≤ 2 →
      (∀ d, |G.coeff d| ≤ N k ^ (10 * s₀)) →
      |F.L 2| ≤ N k ^ (5 * s₀) → |F.L 3| ≤ N k ^ (5 * s₀) →
      |F.c 4| ≤ N k ^ η →
      ∀ (key : Fin 3 → ℤ) (t Z Y z : ℝ), |t| ≤ 1 → |Y| ≤ N k ^ η →
      |Z - domZ (N k ^ (-M)) key t| ≤ 2 * N k ^ (-M) →
      |F.resid t Z Y (eval ![t, Y] G) -
        Support.quadZ (baseCoefficients (nativeChartPolynomial F Q G (N k ^ (-M)) key))
          (F.zt t) z -
        Support.transv (transverseCoefficients (nativeChartPolynomial F Q G (N k ^ (-M)) key))
          (F.zt t) z (F.U t Z Y)| ≤ N k ^ (-M / 2) := by
  filter_upwards [eventually_full_residual_chart_replacement N hN hNt hs₀ hsp hM] with k hk
  intro η hη₀ hη F hq hg ha Q hQ G hG hcoeff hL₂ hL₃ hc₄ key t Z Y z ht hY hZ
  apply native_prediction_error F hq hg Q hQ G hG (N k ^ (-M)) key t Z Y z
  rw [ha]
  exact hk η hη₀ hη G hG F.L hcoeff hL₂ hL₃ t Z _ Y (F.c 4) ht hY hc₄ hZ

end KeyFrame

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
