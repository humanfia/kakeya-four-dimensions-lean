import Submission.Obl.k4_wide_three_layer_scalar_inputs.ComparisonLoss
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Parameters
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortKeyNumerics
import Submission.Obl.k4_wide_three_layer_scalar_inputs.RawScaleNumerics
import Submission.Obl.k4_wide_three_layer_scalar_inputs.WideScaleBudget

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Filter Inherited.Native
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The numerical inputs of the actual comparison, simultaneously at
the three original hidden depths and the one coarse time length. -/
structure ComparisonNumerics
    (N K d κ s₀ s u v M e₀ σ η ξ ηmatch R₀ q : ℝ) : Prop where
  input_one : 1 ≤ N ^ σ
  input_budget : 160 * N ^ σ ≤ N ^ η
  native_budget : K ≤ N ^ η
  input_small : σ ≤ u / 10
  strong_gain : 50 * η ≤ (ξ - 2 * η) * ηmatch
  short : ShortNumerics N (N ^ η) q (N ^ (-s)) (N ^ (-κ * s))
    (N ^ (-2 * κ * s₀)) (N ^ (-M)) (N ^ (-e₀)) (N ^ (-M / 4)) (N ^ (-2 * M))
    (N ^ (10 * s₀)) (N ^ (5 * s₀)) (4 * N ^ η)
  native_accuracy : K * N ^ (-s) ≤ 1
  strip_drift : N ^ (-e₀) + N ^ (-M) ≤ N ^ (-2 * κ * s₀) / 4
  whole_key_strip : 4 * (q * N ^ (-κ * s)) + q * (N ^ (-e₀) + N ^ (-M)) ≤
    4 * N ^ (-2 * κ * s₀)
  raw : ∀ h : Fin 3,
    RawShortBudget (N ^ s₀) (N ^ η) K q (N ^ (-(![s, s + u, s + v] h))) (N ^ (-κ * s))
      (N ^ (-2 * κ * s₀)) (N ^ (-M)) (N ^ (-e₀)) (N ^ σ)
  keys : ∀ (h : Fin 3) (t₀ : ℝ) (key : Fin 3 → ℤ),
    0 ≤ t₀ ∧ t₀ + q ≤ 1 → |(key 0 : ℝ) * N ^ (-M)| ≤ 4 * N ^ η →
    |(key 1 : ℝ) * N ^ (-M)| ≤ 4 * N ^ η →
    ∀ W₁ W₂ : ℝ, 1 ≤ W₁ → W₁ ≤ 2 * N ^ η → 1 ≤ W₂ → W₂ ≤ 2 * N ^ η →
      KeyNum N K d (2 * M) M (![s, s + u, s + v] h) (![s, s + u, s + v] h - 2 * η)
        t₀ q (q * N ^ (-κ * s)) (N ^ (-e₀)) (4 * N ^ η)
        (N ^ (-(![s, s + u, s + v] h))) (2 * N ^ η) (N ^ (10 * η)) (N ^ (10 * s₀))
        W₁ W₂ (4 * N ^ η) (N ^ ξ) (N ^ (20 * η)) (N ^ (-M / 4)) ηmatch R₀ key
  table_loss : ∀ (b : ℝ) (p : Fin 3 → ℝ), 0 ≤ b → b ≤ 140 * K ^ 3 →
    (∀ h, 0 ≤ p h) → (∀ h, p h ≤ 6 * N ^ (2 * σ)) →
    b / N ^ (10 * η) + (∑ h, p h / N ^ (10 * η)) +
      N ^ (20 * η) * (N ^ ξ / (4 * N ^ η)) ^ (-ηmatch) * (b + p 0) ≤ N ^ (-η) ∧
      N ^ (-η) + N ^ (-η) ≤ N ^ (-σ)
  wide : 98304 * (N ^ (σ + (10 / (1 - d)) * u) * N ^ (-s)) *
    (q + (q * N ^ (-κ * s)) / N ^ (-2 * κ * s₀)) ≤ N ^ (-(s + u))

/-- A single positive loss window supplies every numerical field above.
The supplied projected exponents stay fixed before both loss parameters. -/
theorem eventually_comparisonNumerics {N : ℕ → ℝ}
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    {d κ U e₀ buffer ξ ηmatch R₀ : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : 100 < buffer) (p : Parameters d κ U e₀ buffer)
    (hξ : 0 < ξ) (hmatch : 0 < ηmatch) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ σ : ℝ, 0 < σ → 100 * σ ≤ η →
      ∀ᶠ k in atTop, ∀ K q : ℝ, 1 ≤ K → K ≤ N k ^ σ →
        N k ^ (-κ * p.s) / K ≤ q → q ≤ K * N k ^ (-κ * p.s) →
          ComparisonNumerics (N k) K d κ p.s₀ p.s p.u p.v p.M e₀ σ η ξ ηmatch R₀ q := by
  have hM : 100 * p.s₀ < p.M :=
    (mul_lt_mul_of_pos_right hb p.s₀_pos).trans p.M_lower
  have hM0 : 0 < p.M := by linarith [p.s₀_pos]
  have he₀ : 100 * p.M < e₀ :=
    (mul_lt_mul_of_pos_right hb hM0).trans p.M_e
  have hdepth : ∀ h : Fin 3,
      p.s ≤ (![p.s, p.s + p.u, p.s + p.v] h) ∧
      (![p.s, p.s + p.u, p.s + p.v] h) < 3 * p.s₀ / 2 := by
    intro h
    fin_cases h
    · change p.s ≤ p.s ∧ p.s < 3 * p.s₀ / 2
      constructor <;> linarith [p.u_pos, p.su_s₀]
    · change p.s ≤ p.s + p.u ∧ p.s + p.u < 3 * p.s₀ / 2
      constructor <;> linarith [p.u_pos, p.su_s₀]
    · change p.s ≤ p.s + p.v ∧ p.s + p.v < 3 * p.s₀ / 2
      constructor <;> linarith [p.v_pos, p.v_u, p.su_s₀]
  have numEach := fun h : Fin 3 => eventually_shortKeyNumerics_tolerances hN hNt hd0 hd1
    hκ hκ1 p.s₀_pos p.s₀_s (hdepth h).1 (hdepth h).2 hM he₀ hξ hmatch (R₀ := R₀)
  choose ηnum hηnum hnum using numEach
  have rawEach := fun h : Fin 3 => eventually_rawShortBudgets hN hNt hκ hκ1
    p.s₀_pos p.s₀_s (hdepth h).1 (hdepth h).2 hM he₀
  choose ηraw hηraw hraw using rawEach
  obtain ⟨ηshort, hηshort, hshort⟩ := shortNumericsAtHiddenDepthStatement N hN hNt
    κ p.s₀ p.s p.s p.M e₀ hκ hκ1 p.s₀_pos p.s₀_s le_rfl (hdepth 0).2 hM he₀
  let η₀ := min ηshort (min (ηnum 0) (min (ηnum 1) (min (ηnum 2)
    (min (ηraw 0) (min (ηraw 1) (min (ηraw 2)
      (min (ξ / 8) (min (ξ * ηmatch / 100) p.u))))))))
  have hη₀ : 0 < η₀ := by
    dsimp [η₀]
    exact lt_min hηshort (lt_min (hηnum 0) (lt_min (hηnum 1) (lt_min (hηnum 2)
      (lt_min (hηraw 0) (lt_min (hηraw 1) (lt_min (hηraw 2)
        (lt_min (by positivity) (lt_min (by positivity) p.u_pos))))))))
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηη₀ σ hσ hση
  obtain ⟨hηs, hηn0, hηn1, hηn2, hηr0, hηr1, hηr2, hηξ, hηgain, hηu⟩ :
      η ≤ ηshort ∧ η ≤ ηnum 0 ∧ η ≤ ηnum 1 ∧ η ≤ ηnum 2 ∧
      η ≤ ηraw 0 ∧ η ≤ ηraw 1 ∧ η ≤ ηraw 2 ∧
      η ≤ ξ / 8 ∧ η ≤ ξ * ηmatch / 100 ∧ η ≤ p.u := by
    simpa only [η₀, le_min_iff] using hηη₀
  have hσu : σ ≤ p.u / 10 := by linarith
  have hση' : σ < η := by linarith
  have hgain : 50 * η ≤ (ξ - 2 * η) * ηmatch := by
    nlinarith [mul_le_mul_of_nonneg_right hηξ hmatch.le]
  filter_upwards [hshort η hη hηs, hnum 0 η hη hηn0, hnum 1 η hη hηn1,
    hnum 2 η hη hηn2, hraw 0 η hη hηr0, hraw 1 η hη hηr1, hraw 2 η hη hηr2,
    hNt.eventually (eventually_const_mul_rpow_le 160 hση'),
    eventually_short_wide_bound hN hNt p.u_pos hσ hσu p.wide_variation p.wide_block,
    eventually_short_comparison_loss hN hNt hσ hη hση hmatch hgain]
      with k hs hn0 hn1 hn2 hr0 hr1 hr2 h160 hw htab
  intro K q hK hKN hqlo hqhi
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hKH : K ≤ N k ^ η := hKN.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 hση'.le)
  have hP : 1 ≤ N k ^ σ := Real.one_le_rpow hN1 hσ.le
  have hr := hr0 K q hK hKH hqlo hqhi
  refine {
    input_one := hP
    input_budget := h160
    native_budget := hKH
    input_small := hσu
    strong_gain := hgain
    short := hs K q hK hKH hqlo hqhi
    native_accuracy := hr.1
    strip_drift := hr.2.1
    whole_key_strip := hr.2.2.1
    raw := ?_
    keys := ?_
    wide := hw K q hKN hqhi
    table_loss := fun b pp hb0 hbK hp0 hpN => htab K b pp hK hKN hb0 hbK hp0 hpN }
  · intro h
    fin_cases h
    · exact (hr0 K q hK hKH hqlo hqhi).2.2.2 _ hP h160
    · exact (hr1 K q hK hKH hqlo hqhi).2.2.2 _ hP h160
    · exact (hr2 K q hK hKH hqlo hqhi).2.2.2 _ hP h160
  · intro h
    fin_cases h
    · exact hn0 K q hK hKH hqlo hqhi
    · exact hn1 K q hK hKH hqlo hqhi
    · exact hn2 K q hK hKH hqlo hqhi

end Submission.Obl.k4_wide_three_layer_scalar_inputs
