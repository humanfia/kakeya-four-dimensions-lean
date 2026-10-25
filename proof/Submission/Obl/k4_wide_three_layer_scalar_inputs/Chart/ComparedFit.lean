import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.NativePrediction

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial Filter
open Inherited.Native

noncomputable section

namespace KeyFrame

/-- Combine a fine projected fit and its frozen offset from the coarse sheet. -/
theorem fit_and_frozen_offset {X Vfine Vcoarse a D E W : ℝ}
    (hfit : |X - Vfine| ≤ E) (hfreeze : |Vfine - Vcoarse - a * D| ≤ W) :
    |X - Vcoarse - a * D| ≤ E + W := by
  calc
    _ = |(X - Vfine) + (Vfine - Vcoarse - a * D)| := by congr 1; ring
    _ ≤ |X - Vfine| + |Vfine - Vcoarse - a * D| := abs_add_le _ _
    _ ≤ _ := add_le_add hfit hfreeze

/-- Direct original-line fit in the exact `ComparedBlock` coordinates. The only errors
are the original fine fit, the whole-domain frozen offset, and an explicit physical
coefficient bound times the original key width. -/
theorem native_compared_fit {α : Type} [MeasurableSpace α]
    (F : Support.Frame) (b : α → Fin 6 → ℝ) (l : α)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Inherited.Native.HorizontalForm Q F.L)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    (Gfine : MvPolynomial (Fin 2) ℝ) (key : Fin 3 → ℤ)
    {χ t H B Lb D E W : ℝ}
    (hq : F.q ≠ 0) (hg : F.g ≠ 0) (ha : 0 < F.a)
    (hχ : 0 < χ) (hχ₁ : χ ≤ 1) (hH : 1 ≤ H)
    (hkey : slotKey b χ (F.q * F.g) F.t₀ l = key)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ d, |G.coeff d| ≤ B) (hL₂ : |F.L 2| ≤ Lb) (hL₃ : |F.L 3| ≤ Lb)
    (hY : |b l 1 + t * b l 4| ≤ H) (hc₄ : |F.c 4| ≤ H)
    (hfit : |b l 2 + t * b l 5 - eval ![t, b l 1 + t * b l 4] Gfine| ≤ E)
    (hfreeze : |eval ![t, b l 1 + t * b l 4] Gfine -
      eval ![t, b l 1 + t * b l 4] G - F.a * D| ≤ W) :
    let p := nativeChartPolynomial F.cellFrame Q G χ key
    |F.resid (b l) t - Support.quadZ (baseCoefficients p) (F.zt t) (F.zZ (b l) t) - D -
      Support.transv (transverseCoefficients p) (F.zt t) (F.zZ (b l) t) (F.tr (b l) t)| ≤
      (E + W) / F.a + (6 * B * H ^ 2 + 2 * Lb * H) * (2 * χ) / F.a := by
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hZ := label_Z_near hχ hkey ht
  have herror := physicalResidual_chart_error G hG F.L ha hH hcoeff hL₂ hL₃ ht' hY hc₄ hZ
    (by linarith : 2 * χ ≤ 2)
  have hchart := native_prediction_error F.cellFrame hq hg Q hQ G hG χ key t
    (b l 0 + t * b l 3) (b l 1 + t * b l 4) (F.zZ (b l) t)
    ((6 * B * H ^ 2 + 2 * Lb * H) * (2 * χ) / F.a) herror
  exact residual_fit_of_chart_prediction F.cellFrame ha G _
    (fit_and_frozen_offset hfit hfreeze) hchart

/-- With the fixed horizon paid, the same original-line fit has just the normalized
fine errors and a negligible `N^(-M/2)` chart term. -/
theorem eventually_native_compared_fit (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {s₀ sp M : ℝ}
    (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2) (hM : 100 * s₀ < M) :
    ∀ᶠ k in atTop, ∀ η : ℝ, 0 ≤ η → η ≤ s₀ →
      ∀ (α : Type) [MeasurableSpace α] (F : Support.Frame) (b : α → Fin 6 → ℝ) (l : α),
      F.q ≠ 0 → F.g ≠ 0 → F.a = N k ^ (-sp) →
      ∀ Q : MvPolynomial (Fin 4) ℝ, Inherited.Native.HorizontalForm Q F.L →
      ∀ G : MvPolynomial (Fin 2) ℝ, G.totalDegree ≤ 2 →
      (∀ d, |G.coeff d| ≤ N k ^ (10 * s₀)) →
      |F.L 2| ≤ N k ^ (5 * s₀) → |F.L 3| ≤ N k ^ (5 * s₀) →
      |F.c 4| ≤ N k ^ η →
      ∀ (Gfine : MvPolynomial (Fin 2) ℝ) (key : Fin 3 → ℤ) (t D E W : ℝ),
      slotKey b (N k ^ (-M)) (F.q * F.g) F.t₀ l = key →
      t ∈ Icc (0 : ℝ) 1 → |b l 1 + t * b l 4| ≤ N k ^ η →
      |b l 2 + t * b l 5 - eval ![t, b l 1 + t * b l 4] Gfine| ≤ E →
      |eval ![t, b l 1 + t * b l 4] Gfine -
        eval ![t, b l 1 + t * b l 4] G - F.a * D| ≤ W →
      let p := nativeChartPolynomial F.cellFrame Q G (N k ^ (-M)) key
      |F.resid (b l) t - Support.quadZ (baseCoefficients p) (F.zt t) (F.zZ (b l) t) - D -
        Support.transv (transverseCoefficients p) (F.zt t) (F.zZ (b l) t) (F.tr (b l) t)| ≤
        (E + W) / F.a + N k ^ (-M / 2) := by
  filter_upwards [eventually_native_prediction_error N hN hNt hs₀ hsp hM] with k hk
  intro η hη₀ hη α _ F b l hq hg ha Q hQ G hG hcoeff hL₂ hL₃ hc₄ Gfine key t D E W
    hkey ht hY hfit hfreeze
  have hN₀ : 0 < N k := by linarith [hN k]
  have hχ : 0 < N k ^ (-M) := Real.rpow_pos_of_pos hN₀ _
  have ht' : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hchart := hk η hη₀ hη F.cellFrame hq hg ha Q hQ G hG hcoeff hL₂ hL₃ hc₄
    key t (b l 0 + t * b l 3) (b l 1 + t * b l 4) (F.zZ (b l) t) ht' hY
      (label_Z_near hχ hkey ht)
  exact residual_fit_of_chart_prediction F.cellFrame
    (by change 0 < F.a; rw [ha]; positivity) G _ (fit_and_frozen_offset hfit hfreeze) hchart

end KeyFrame

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
