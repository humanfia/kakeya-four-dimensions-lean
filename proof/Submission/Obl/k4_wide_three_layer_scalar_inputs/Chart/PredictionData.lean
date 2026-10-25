import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.NativeBounds
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.ComparedFit

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MvPolynomial Filter
open Inherited.Native

noncomputable section

namespace KeyFrame

/-- One occupied original key supplies a single bounded prediction, valid at every
original incidence of that key. This is the chart-level input to the block assembly. -/
theorem exists_native_prediction {α : Type} [MeasurableSpace α]
    (F : Support.Frame) (b : α → Fin 6 → ℝ) (l₀ : α) (key : Fin 3 → ℤ)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Inherited.Native.HorizontalForm Q F.L)
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {K Mst χ B Lb : ℝ} (hK : 1 ≤ K) (hMst : 0 ≤ Mst)
    (hq : 0 < F.q) (hg : 0 < F.g) (ha : 0 < F.a)
    (hg₁ : F.g ≤ 1) (hqg : F.q ≤ K * F.g)
    (hχ : 0 < χ) (hχ₁ : χ ≤ 1) (hχm : χ ≤ F.q * F.g)
    (hkey₀ : slotKey b χ (F.q * F.g) F.t₀ l₀ = key)
    (ht₀ : |F.t₀| ≤ 1) (hc₄ : |F.c 4| ≤ K) (hb₃ : |b l₀ 3| ≤ K)
    (hcenter : |F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1| +
      |F.c 4 - (F.t₀ + F.q / 2)| ≤ K * F.q)
    (hQ₀ : |b l₀ 1 + F.t₀ * b l₀ 4 -
      baseY F.cellFrame F.t₀ (b l₀ 0 + F.t₀ * b l₀ 3)| ≤ K * (F.q * F.g))
    (hQmid : |b l₀ 0 + (F.t₀ + F.q / 2) * b l₀ 3 - F.c 0 -
      (F.t₀ + F.q / 2) * F.c 1| ≤ K * F.q)
    (hr : ∀ e, |nativeDiscrepancy F.cellFrame Q G χ key e| ≤ Mst)
    (hcoeff : ∀ d, |G.coeff d| ≤ B) (hL₂ : |F.L 2| ≤ Lb) (hL₃ : |F.L 3| ≤ Lb) :
    ∃ (pc : Fin 6 → ℝ) (tc : Fin 4 → ℝ),
      (∀ e, |pc e| ≤ 3888 * Mst * K ^ 8) ∧
      (∀ e, |tc e| ≤ 3888 * Mst * K ^ 8) ∧ tc 2 = 0 ∧
      ∀ (l : α) (Gfine : MvPolynomial (Fin 2) ℝ) (t D E W : ℝ),
        slotKey b χ (F.q * F.g) F.t₀ l = key → t ∈ Icc (0 : ℝ) 1 →
        |b l 1 + t * b l 4| ≤ 2 * K →
        |b l 2 + t * b l 5 - eval ![t, b l 1 + t * b l 4] Gfine| ≤ E →
        |eval ![t, b l 1 + t * b l 4] Gfine -
          eval ![t, b l 1 + t * b l 4] G - F.a * D| ≤ W →
        |F.resid (b l) t - Support.quadZ pc (F.zt t) (F.zZ (b l) t) - D -
          Support.transv tc (F.zt t) (F.zZ (b l) t) (F.tr (b l) t)| ≤
          (E + W) / F.a + (48 * B * K ^ 2 + 8 * Lb * K) * χ / F.a := by
  have hβ := native_beta_bound F.cellFrame b l₀ key hK hq hg hg₁ hqg hχ hχm
    hkey₀ ht₀ hc₄ hb₃ hcenter hQ₀ hQmid
  have hbounds := native_coefficients_bound F.cellFrame Q G χ key hK hMst hβ hr
  let p := nativeChartPolynomial F.cellFrame Q G χ key
  refine ⟨baseCoefficients p, transverseCoefficients p, hbounds.1, hbounds.2, rfl, ?_⟩
  intro l Gfine t D E W hkey ht hY hfit hfreeze
  have h := native_compared_fit F b l Q hQ G hG Gfine key hq.ne' hg.ne' ha hχ hχ₁
    (by linarith : 1 ≤ 2 * K) hkey ht hcoeff hL₂ hL₃ hY
    (hc₄.trans (by linarith : K ≤ 2 * K)) hfit hfreeze
  convert h using 1 <;> ring

/-- The same bounded prediction has a negligible chart error at the fixed physical
horizon. All frame, graph, label and fine-fit choices remain uniform at each index. -/
theorem eventually_exists_native_prediction (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) {s₀ sp M η : ℝ}
    (hs₀ : 0 < s₀) (hsp : sp < 3 * s₀ / 2) (hM : 100 * s₀ < M)
    (hη : 0 < η) (hηs₀ : 2 * η ≤ s₀) :
    ∀ᶠ k in atTop,
      ∀ (α : Type) [MeasurableSpace α] (F : Support.Frame) (b : α → Fin 6 → ℝ)
        (l₀ : α) (key : Fin 3 → ℤ) (Q : MvPolynomial (Fin 4) ℝ)
        (G : MvPolynomial (Fin 2) ℝ) (K Mst : ℝ),
      Inherited.Native.HorizontalForm Q F.L → G.totalDegree ≤ 2 →
      1 ≤ K → K ≤ N k ^ η → 0 ≤ Mst →
      0 < F.q → 0 < F.g → F.a = N k ^ (-sp) →
      F.g ≤ 1 → F.q ≤ K * F.g → N k ^ (-M) ≤ F.q * F.g →
      slotKey b (N k ^ (-M)) (F.q * F.g) F.t₀ l₀ = key →
      |F.t₀| ≤ 1 → |F.c 4| ≤ K → |b l₀ 3| ≤ K →
      |F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1| +
        |F.c 4 - (F.t₀ + F.q / 2)| ≤ K * F.q →
      |b l₀ 1 + F.t₀ * b l₀ 4 -
        baseY F.cellFrame F.t₀ (b l₀ 0 + F.t₀ * b l₀ 3)| ≤ K * (F.q * F.g) →
      |b l₀ 0 + (F.t₀ + F.q / 2) * b l₀ 3 - F.c 0 -
        (F.t₀ + F.q / 2) * F.c 1| ≤ K * F.q →
      (∀ e, |nativeDiscrepancy F.cellFrame Q G (N k ^ (-M)) key e| ≤ Mst) →
      (∀ d, |G.coeff d| ≤ N k ^ (10 * s₀)) →
      |F.L 2| ≤ N k ^ (5 * s₀) → |F.L 3| ≤ N k ^ (5 * s₀) →
      ∃ (pc : Fin 6 → ℝ) (tc : Fin 4 → ℝ),
        (∀ e, |pc e| ≤ 3888 * Mst * K ^ 8) ∧
        (∀ e, |tc e| ≤ 3888 * Mst * K ^ 8) ∧ tc 2 = 0 ∧
        ∀ (l : α) (Gfine : MvPolynomial (Fin 2) ℝ) (t D E W : ℝ),
          slotKey b (N k ^ (-M)) (F.q * F.g) F.t₀ l = key →
          t ∈ Icc (0 : ℝ) 1 → |b l 1 + t * b l 4| ≤ 2 * K →
          |b l 2 + t * b l 5 - eval ![t, b l 1 + t * b l 4] Gfine| ≤ E →
          |eval ![t, b l 1 + t * b l 4] Gfine -
            eval ![t, b l 1 + t * b l 4] G - F.a * D| ≤ W →
          |F.resid (b l) t - Support.quadZ pc (F.zt t) (F.zZ (b l) t) - D -
            Support.transv tc (F.zt t) (F.zZ (b l) t) (F.tr (b l) t)| ≤
            (E + W) / F.a + N k ^ (-M / 2) := by
  have hgrowth := (tendsto_rpow_atTop hη).comp hNt
  filter_upwards [eventually_native_compared_fit N hN hNt hs₀ hsp hM,
    hgrowth.eventually (eventually_ge_atTop (2 : ℝ))] with k hk htwo
  change 2 ≤ N k ^ η at htwo
  intro α _ F b l₀ key Q G K Mst hQ hG hK hKN hMst hq hg ha hg₁ hqg hχm
    hkey₀ ht₀ hc₄ hb₃ hcenter hQ₀ hQmid hr hcoeff hL₂ hL₃
  have hN₀ : 0 < N k := by linarith [hN k]
  have hN₁ : 1 ≤ N k := by linarith [hN k]
  have hχ : 0 < N k ^ (-M) := Real.rpow_pos_of_pos hN₀ _
  have hβ := native_beta_bound F.cellFrame b l₀ key hK hq hg hg₁ hqg hχ hχm
    hkey₀ ht₀ hc₄ hb₃ hcenter hQ₀ hQmid
  have hbounds := native_coefficients_bound F.cellFrame Q G (N k ^ (-M)) key hK hMst hβ hr
  let p := nativeChartPolynomial F.cellFrame Q G (N k ^ (-M)) key
  refine ⟨baseCoefficients p, transverseCoefficients p, hbounds.1, hbounds.2, rfl, ?_⟩
  have htwoK : 2 * K ≤ N k ^ (2 * η) := by
    calc
      _ ≤ N k ^ η * N k ^ η := mul_le_mul htwo hKN (by linarith) (by positivity)
      _ = _ := by rw [← Real.rpow_add hN₀]; congr 1; ring
  intro l Gfine t D E W hkey ht hY hfit hfreeze
  exact hk (2 * η) (by positivity) hηs₀ α F b l hq.ne' hg.ne' ha Q hQ G hG
    hcoeff hL₂ hL₃ (hc₄.trans ((by linarith : K ≤ 2 * K).trans htwoK))
    Gfine key t D E W hkey ht (hY.trans htwoK) hfit hfreeze

end KeyFrame

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
