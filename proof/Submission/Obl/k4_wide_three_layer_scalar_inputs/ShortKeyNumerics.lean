import Submission.Obl.k4_wide_three_layer_scalar_inputs.KeyNumerics
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortNumericsProof
import Submission.Obl.k4_wide_three_layer_scalar_inputs.MatchingBudgets

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter Inherited.Native

/-- One loss window supplies every numerical hypothesis for the actual
short-key matching, uniformly over native dyadic time lengths and all
occupied key centers. The hidden depth may be finer than the time depth. -/
theorem eventually_shortKeyNumerics_tolerances {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d κ s₀ s sp M e₀ ξ ηmatch R₀ : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hs₀ : 0 < s₀) (hs₀s : s₀ < s) (hssp : s ≤ sp) (hsp : sp < 3 * s₀ / 2)
    (hM : 100 * s₀ < M) (he₀ : 100 * M < e₀) (hξ : 0 < ξ) (hmatch : 0 < ηmatch) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ᶠ k in atTop, ∀ K q : ℝ, 1 ≤ K → K ≤ N k ^ η →
        (N k ^ (-κ * s)) / K ≤ q → q ≤ K * N k ^ (-κ * s) →
        ∀ (t₀ : ℝ) (key : Fin 3 → ℤ),
          0 ≤ t₀ ∧ t₀ + q ≤ 1 →
          |(key 0 : ℝ) * N k ^ (-M)| ≤ 4 * N k ^ η →
          |(key 1 : ℝ) * N k ^ (-M)| ≤ 4 * N k ^ η →
          ∀ W₁ W₂ : ℝ, 1 ≤ W₁ → W₁ ≤ 2 * N k ^ η → 1 ≤ W₂ → W₂ ≤ 2 * N k ^ η →
          KeyNum (N k) K d (2 * M) M sp (sp - 2 * η) t₀ q
            (q * N k ^ (-κ * s)) (N k ^ (-e₀)) (4 * N k ^ η) (N k ^ (-sp))
            (2 * N k ^ η) (N k ^ (10 * η)) (N k ^ (10 * s₀))
            W₁ W₂ (4 * N k ^ η) (N k ^ ξ) (N k ^ (20 * η))
            (N k ^ (-M / 4)) ηmatch R₀ key := by
  obtain ⟨ηs, hηs, hshort⟩ := shortNumericsAtHiddenDepthStatement N hN hNt κ s₀ s sp M e₀
    hκ hκ1 hs₀ hs₀s hssp hsp hM he₀
  have hsp0 : 0 < sp := hs₀.trans_le (hs₀s.le.trans hssp)
  let η₀ := min ηs (min (sp / 8) (min (ξ / 8) (ξ * ηmatch / 100)))
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηη₀
  have hηshort : η ≤ ηs := hηη₀.trans (min_le_left _ _)
  have hηsp : η ≤ sp / 8 := hηη₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηξ : η ≤ ξ / 8 :=
    hηη₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηgain : η ≤ ξ * ηmatch / 100 :=
    hηη₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hgain : 20 * η ≤ (ξ - 2 * η) * ηmatch := by
    have hsmall := mul_le_mul_of_nonneg_right hηξ hmatch.le
    nlinarith
  filter_upwards [hshort η hη hηshort,
    eventually_matchingBudgets hN hNt hd0 hd1 hs₀ hη hξ hmatch hgain (le_refl sp)]
    with k hsk hbk
  intro K q hK hKH hqlo hqhi t₀ key hunit hL0 hL1 W₁ W₂ hW₁1 hW₁H hW₂1 hW₂H
  have hnums := hsk K q hK hKH hqlo hqhi
  have hb := hbk K hK hKH
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hH : 1 ≤ N k ^ η := Real.one_le_rpow hN1 hη.le
  have hq : 0 < q := (div_pos (Real.rpow_pos_of_pos hNp _) (by linarith : 0 < K)).trans_le hqlo
  exact keyNum_of_shortNumerics_tolerances hnums (by linarith [hN k]) hH (by linarith) hd0 hd1 hq
    (Real.rpow_pos_of_pos hNp _) (Real.rpow_pos_of_pos hNp _)
    (Real.rpow_nonneg hNp.le _) (by positivity) hb.coefficient_two (by positivity)
    (by positivity) rfl (by congr 1; ring) hsp0.le (by linarith) (by linarith) hunit hL0 hL1
    hb.match_two hb.graph_match hb.matching_cutoff
    (Real.one_le_rpow hN1 (by positivity)) hb.matching_gain hb.fit_resolution
    hb.cap_budget hb.horizon hb.jet_budget hW₁1 hW₁H hW₂1 hW₂H

/-- The common tolerance used by the finer offset count. -/
theorem eventually_shortKeyNumerics {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d κ s₀ s sp M e₀ ξ ηmatch R₀ : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hs₀ : 0 < s₀) (hs₀s : s₀ < s) (hssp : s ≤ sp) (hsp : sp < 3 * s₀ / 2)
    (hM : 100 * s₀ < M) (he₀ : 100 * M < e₀) (hξ : 0 < ξ) (hmatch : 0 < ηmatch) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ᶠ k in atTop, ∀ K q : ℝ, 1 ≤ K → K ≤ N k ^ η →
        (N k ^ (-κ * s)) / K ≤ q → q ≤ K * N k ^ (-κ * s) →
        ∀ (t₀ : ℝ) (key : Fin 3 → ℤ),
          0 ≤ t₀ ∧ t₀ + q ≤ 1 →
          |(key 0 : ℝ) * N k ^ (-M)| ≤ 4 * N k ^ η →
          |(key 1 : ℝ) * N k ^ (-M)| ≤ 4 * N k ^ η →
          KeyNum (N k) K d (2 * M) M sp (sp - 2 * η) t₀ q
            (q * N k ^ (-κ * s)) (N k ^ (-e₀)) (4 * N k ^ η) (N k ^ (-sp))
            (2 * N k ^ η) (N k ^ (10 * η)) (N k ^ (10 * s₀))
            (2 * N k ^ η) (2 * N k ^ η) (4 * N k ^ η) (N k ^ ξ) (N k ^ (20 * η))
            (N k ^ (-M / 4)) ηmatch R₀ key := by
  obtain ⟨η₀, hη₀, hall⟩ := eventually_shortKeyNumerics_tolerances hN hNt hd0 hd1 hκ hκ1
    hs₀ hs₀s hssp hsp hM he₀ hξ hmatch (R₀ := R₀)
  refine ⟨η₀, hη₀, fun η hη hηη₀ => ?_⟩
  filter_upwards [hall η hη hηη₀] with k hk
  intro K q hK hKH hqlo hqhi t₀ key hunit hL0 hL1
  have hH : 1 ≤ N k ^ η := Real.one_le_rpow (by linarith [hN k]) hη.le
  exact hk K q hK hKH hqlo hqhi t₀ key hunit hL0 hL1 (2 * N k ^ η) (2 * N k ^ η)
    (by linarith) le_rfl (by linarith) le_rfl

end Submission.Obl.k4_wide_three_layer_scalar_inputs
