import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CoreOfBig

/-!
# Proof of the single-sample supercritical return

Scalar is applied with terminal exponent `s₁ - s₀`, mesh exponent `M + 4 s₀`, density range
`s₁ + 1`, angular range `s₁ - s₀` and tolerance `min (ε/4) 1`; then the pruning exponent
`η₁` and the sample exponent `η = η₁/100` are chosen below all the margins, and every sample
with `N` beyond the last threshold is handled by `core_of_big`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem coreStatement_holds : CoreStatement := by
  intro hScalar d κ S e₀ s₀ s₁ vc M RL Rout ε hd0 hd1 hκ hκ1 hS0 hS1 hs₀ hs₀₁ hs₁ hvc0 hvc hes hM
    hRL hRout hε
  set εS := min (ε / 4) 1 with hεSdef
  have hεS0 : 0 < εS := lt_min (by linarith) one_pos
  have hs : 0 < s₁ - s₀ := by linarith
  have hsm : s₁ - s₀ < M + 4 * s₀ := by rw [hM]; linarith
  obtain ⟨ηS, hηS, N₀S, hN₀S, hSA⟩ := scalarAt_of_scalar hScalar (s := s₁ - s₀) (m := M + 4 * s₀)
    (C := s₁ + 1) (U := s₁ - s₀) (ε := εS) hd0 hd1 hs hsm (by linarith) hS0 hs hsm hεS0
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_stripBound
  set p := 1 / (1 - d) with hp
  have hp0 : 0 < p := by rw [hp]; apply div_pos one_pos; linarith
  set mg := (2 * κ - 1) * (s₁ - s₀) / 2 with hmg
  have hmg0 : 0 < mg := by
    rw [hmg]; have : 0 < 2 * κ - 1 := by linarith
    positivity
  set η₁ := min (min (ηS / 100) (s₀ / 1000)) (min 1 (mg / 40 / p)) with hη₁def
  have hη₁0 : 0 < η₁ := lt_min (lt_min (by positivity) (by positivity))
    (lt_min one_pos (by positivity))
  set η := η₁ / 100 with hηdef
  have hη0 : 0 < η := by positivity
  set Rcap := M + 4 * s₀ + s₁ + 10 + 10 / ηS + 1 / s₀ with hRcapdef
  have hR10 : M + 4 * s₀ + s₁ + 10 ≤ Rcap := by
    have : 0 ≤ 10 / ηS + 1 / s₀ := by positivity
    rw [hRcapdef]; linarith
  have hRS : 10 / ηS ≤ Rcap := by
    have : 0 ≤ M + 4 * s₀ + s₁ + 10 := by rw [hM]; linarith
    have : 0 ≤ 1 / s₀ := by positivity
    rw [hRcapdef]; linarith
  have hRs₀ : 1 / s₀ ≤ Rcap := by
    have : 0 ≤ M + 4 * s₀ + s₁ + 10 := by rw [hM]; linarith
    have : 0 ≤ 10 / ηS := by positivity
    rw [hRcapdef]; linarith
  have hRpos : 0 < Rcap := lt_of_lt_of_le (by positivity) hRs₀
  have hRinv : Rcap⁻¹ ≤ s₀ := by
    rw [inv_le_comm₀ hRpos hs₀]; rwa [one_div] at hRs₀
  have hE : ExpOK d κ S s₀ s₁ vc M ε Rout η η₁ ηS εS Rcap := {
    d0 := hd0
    d1 := hd1
    κ2 := hκ
    κ1 := hκ1
    S0 := hS0
    S1 := hS1
    s₀0 := hs₀
    s₀₁ := hs₀₁
    s₁lt := hs₁
    vc0 := hvc0
    vcle := hvc
    hM := hM
    Rout := hRout
    ε0 := hε
    η0 := hη0.le
    ηη₁ := rfl
    η₁0 := hη₁0
    η₁S := (min_le_left _ _).trans (min_le_left _ _)
    η₁s₀ := (min_le_left _ _).trans (min_le_right _ _)
    η₁1 := (min_le_right _ _).trans (min_le_left _ _)
    η₁m := by
      have h : η₁ ≤ mg / 40 / p :=
        (min_le_right (min (ηS / 100) (s₀ / 1000)) (min 1 (mg / 40 / p))).trans
          (min_le_right 1 (mg / 40 / p))
      have : η₁ * p ≤ mg / 40 := by
        calc η₁ * p ≤ mg / 40 / p * p := mul_le_mul_of_nonneg_right h hp0.le
          _ = mg / 40 := by field_simp
      rw [hp, hmg] at this; exact this
    ηS0 := hηS
    εS0 := hεS0.le
    εSε := by have := min_le_left (ε / 4) 1; rw [← hεSdef] at this; linarith
    εS1 := min_le_right _ _
    Rinv := hRinv
    Rbig := hR10
    RS := hRS }
  obtain ⟨N₀, hN₀2, hbig⟩ := exists_bigN hE hC₀pos
  refine ⟨η, hη0, max N₀ N₀S, le_trans hN₀2 (le_max_left _ _), Rcap,
    by linarith [hR10, hM, hs₀, hs₀₁], hRinv, by linarith [hR10, hs₀, hs₀₁], ?_⟩
  intro N hN K εL hK1 hKη hεL0 hεLη α _ ν μ ρ ρs π b f₀ fc fe Ly hb hνp hπp hμ hρμ hsupp hbbd hx3
    hhor hcaps hf₀ hfc hfe hn0 hn1 hρs hρsm hρscov hLy
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNS : N₀S ≤ N := le_trans (le_max_right _ _) hN
  let D : CoreData α := ⟨N, K, d, κ, S, e₀, s₀, s₁, vc, M, RL, εL, Rcap, ν, μ, ρ, ρs, π, b, f₀, fc,
    fe, Ly⟩
  have H : CoreHyp D := {
    N2 := le_trans hN₀2 hNN₀
    K1 := hK1
    bmeas := hb
    νprob := hνp
    πprob := hπp
    μdom := hμ
    ρμ := hρμ
    μsupp := hsupp
    bbd := hbbd
    x3bd := hx3
    hor := hhor
    caps := hcaps
    f₀good := hf₀
    fcgood := hfc
    fegood := hfe
    nest0 := hn0
    nest1 := hn1
    ρsρ := hρs
    ρsmass := hρsm
    ρscov := hρscov
    lygood := hLy }
  exact core_of_big D H hSA hNS hC₀ hC₀pos hE (hbig N hNN₀) hKη hεL0 hεLη

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
