import Submission.Obl.k4_wide_three_layer_scalar_inputs.RawShortBudget
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortNumericsProof

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The literal graph and strip hypotheses of the global short comparison
hold at every sufficiently small loss, uniformly over native dyadic time
lengths and all smaller input norms. -/
theorem eventually_rawShortBudgets {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {κ s₀ s sp M e₀ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hs₀ : 0 < s₀) (hs₀s : s₀ < s) (hssp : s ≤ sp) (hsp : sp < 3 * s₀ / 2)
    (hM : 100 * s₀ < M) (he₀ : 100 * M < e₀) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ᶠ k in atTop, ∀ K q : ℝ, 1 ≤ K → K ≤ N k ^ η →
        N k ^ (-κ * s) / K ≤ q → q ≤ K * N k ^ (-κ * s) →
        K * N k ^ (-sp) ≤ 1 ∧
        N k ^ (-e₀) + N k ^ (-M) ≤ N k ^ (-2 * κ * s₀) / 4 ∧
        4 * (q * N k ^ (-κ * s)) + q * (N k ^ (-e₀) + N k ^ (-M)) ≤
          4 * N k ^ (-2 * κ * s₀) ∧
        ∀ P : ℝ, 1 ≤ P → 160 * P ≤ N k ^ η →
          RawShortBudget (N k ^ s₀) (N k ^ η) K q (N k ^ (-sp)) (N k ^ (-κ * s))
            (N k ^ (-2 * κ * s₀)) (N k ^ (-M)) (N k ^ (-e₀)) P := by
  obtain ⟨ηs, hηs, hshort⟩ := shortNumericsAtHiddenDepthStatement N hN hNt κ s₀ s sp M e₀
    hκ hκ1 hs₀ hs₀s hssp hsp hM he₀
  have hs : 0 < s := hs₀.trans hs₀s
  have hsp0 : 0 < sp := hs.trans_le hssp
  have hM0 : 0 < M := by linarith
  have hκs : κ * s ≤ s := mul_le_of_le_one_left hs.le hκ1
  have hκs₀ : κ * s₀ ≤ s₀ := mul_le_of_le_one_left hs₀.le hκ1
  let η₀ := min ηs (min (s₀ / 100) (κ * (s - s₀) / 2))
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηη₀
  have hηshort : η ≤ ηs := hηη₀.trans (min_le_left _ _)
  have hηs₀ : η ≤ s₀ / 100 := hηη₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηgap : η ≤ κ * (s - s₀) / 2 := hηη₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : η - 2 * κ * s < -2 * κ * s₀ := by nlinarith
  have hstrip : -M < -2 * κ * s₀ := by linarith
  filter_upwards [hshort η hη hηshort,
    hNt.eventually (eventually_const_mul_rpow_le 10000 (a := 0) (b := s₀) hs₀),
    hNt.eventually (eventually_const_mul_rpow_le 2 hgap),
    hNt.eventually (eventually_const_mul_rpow_le 8 hstrip)] with k hsk hRbig hhalf hdrift
  intro K q hK hKH hqlo hqhi
  have hNum := hsk K q hK hKH hqlo hqhi
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hH : 1 ≤ N k ^ η := Real.one_le_rpow hN1 hη.le
  have hg : 0 < N k ^ (-κ * s) := Real.rpow_pos_of_pos hNp _
  have ha : 0 < N k ^ (-sp) := Real.rpow_pos_of_pos hNp _
  have hD : 0 < N k ^ (-2 * κ * s₀) := Real.rpow_pos_of_pos hNp _
  have hK0 : 0 < K := by linarith
  have hq : 0 < q := (div_pos hg hK0).trans_le hqlo
  have hζχ : N k ^ (-e₀) ≤ N k ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hmhalf : q * N k ^ (-κ * s) ≤ N k ^ (-2 * κ * s₀) / 2 := by
    have hh : q * N k ^ (-κ * s) ≤ N k ^ (η - 2 * κ * s) := by
      calc _ ≤ (N k ^ η * N k ^ (-κ * s)) * N k ^ (-κ * s) := by
            gcongr
            exact hqhi.trans (mul_le_mul_of_nonneg_right hKH hg.le)
        _ = _ := by rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; congr 1; ring
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc K * N k ^ (-sp) ≤ N k ^ η * N k ^ (-sp) := mul_le_mul_of_nonneg_right hKH ha.le
      _ = N k ^ (η - sp) := by rw [← Real.rpow_add hNp]; congr 1
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  · linarith
  · have hsmall : q * (N k ^ (-e₀) + N k ^ (-M)) ≤ (q * N k ^ (-κ * s)) / 4 := by
      have hh := mul_le_mul_of_nonneg_left hNum.jitter_quarter (mul_pos hq hg).le
      exact hNum.interval_drift.trans (by nlinarith)
    linarith
  · intro P hP hPH
    have hRpow (j : ℕ) : (N k ^ s₀) ^ j = N k ^ (s₀ * j) :=
      (Real.rpow_mul_natCast hNp.le _ _).symm
    have hbase : 1 / (N k ^ s₀) ^ 2 = N k ^ (-2 * s₀) := by
      rw [hRpow, one_div, ← Real.rpow_neg hNp.le]
      congr 1
      ring
    have hqbase : N k ^ (-κ * s - η) ≤ q := by
      calc _ = N k ^ (-κ * s) / N k ^ η := by rw [← Real.rpow_sub hNp]
        _ ≤ N k ^ (-κ * s) / K := div_le_div_of_nonneg_left hg.le hK0 hKH
        _ ≤ q := hqlo
    have hqloR : 1 / (N k ^ s₀) ^ 2 ≤ q := by
      rw [hbase]
      exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hqbase
    have haloR : 1 / (N k ^ s₀) ^ 2 ≤ N k ^ (-sp) := by
      rw [hbase]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hH6 : (N k ^ η) ^ 6 ≤ N k ^ s₀ := by
      rw [← Real.rpow_mul_natCast hNp.le]
      exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num; linarith)
    have hNumR : ShortNumerics (N k) (N k ^ η) q (N k ^ (-sp)) (N k ^ (-κ * s))
        (N k ^ (-2 * κ * s₀)) (N k ^ (-M)) (N k ^ (-e₀))
        (N k ^ (-M / 4)) (N k ^ (-2 * M)) ((N k ^ s₀) ^ 10) ((N k ^ s₀) ^ 5)
        (4 * N k ^ η) := by
      convert hNum using 1 <;> rw [hRpow] <;> congr 1 <;> ring
    exact rawShortBudget_of_polynomial_budget hNumR (by simpa using hRbig) hH
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hH6 hK hKH hq hg ha hD
      hqloR haloR (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
      (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith [mul_pos hκ hs₀])) (by positivity) (by positivity) hP hPH

end Submission.Obl.k4_wide_three_layer_scalar_inputs
