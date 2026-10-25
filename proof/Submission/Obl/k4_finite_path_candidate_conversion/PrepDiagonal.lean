-- Adapted from this LOT tree, o199, session x0700, commit c97a284c,
-- Submission/Obl/k4_finite_path_candidate_conversion/PrepDiagonal.lean.

import Submission.Obl.k4_finite_path_candidate_conversion.Stages
import Submission.Obl.k4_finite_path_candidate_conversion.EStages

/-!
# The stage diagonal of the preparation child (`PreparationStatement`)

`StageModel … n m s gain δ₀` has the quantifier prefix of `Discovery` (same data, same choice of
`Mc`, `σ k₀` after the loss `ε`, same positive path and residual `H`), but instead of a candidate
it supplies, at that sample, one index `st` of the general prepared model (single parent,
`α` the lines) with `N ≥ n + 2`, `1 ≤ K ≤ N^(1/(n+1))`, `EH1`, and `EH2 … EH4` for every range
`R ≤ n`, and it returns every model candidate of range `R ≤ n` and loss `ε' ≤ ρ/(4R)` to a
`MixedCandidate` in `H`.

`preparation_of_stageModel`: the frozen `E false` plus such a model at every stage `n` give
`PreparationStatement`. If discovery failed on every fine grid, the failures at the stage grids
give one model index per stage, without candidates; the stages satisfy the model hypotheses along
`n`, so the principle gives candidates of one range `R` at arbitrarily late stages, which the
return contradicts.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_path_candidate_conversion

open MeasureTheory

noncomputable section

/-- A model index prepared for stage `n` (`N` large, `K` subpower at rate `1/(n+1)`, the
pointwise hypotheses, and the range hypotheses up to `R = n`). -/
def StageGood (d₁ κ₁ ℓ S : ℝ) (n : ℕ) (st : EStage (ℕ × (Fin 6 → ℝ))) : Prop :=
  ((n : ℝ) + 2 ≤ st.N) ∧ (1 ≤ st.K ∧ st.K ≤ st.N ^ (1 / ((n : ℝ) + 1))) ∧ EH1 st ∧
    (∀ R : ℝ, 1 < R → R ≤ n → EH2 d₁ S st R ∧ EH3 d₁ κ₁ ℓ 1 1 st R ∧ EH4 1 st R)

/-- The preparation of one stage `n` on the grid `m, s` with gains `gain, δ₀`. -/
def StageModel (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ) : Prop :=
  ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mc : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
    ∀ r T nw κ C lev par γ j c u Q R A F lst,
      PositivePath ℓ (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
        Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧
          H w ⊆ TerminalInc (W k) C m lev γ F w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod MeasureTheory.volume) (TerminalInc (W k) C m lev γ F w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod MeasureTheory.volume) (H w) →
        ∃ st : EStage (ℕ × (Fin 6 → ℝ)), StageGood d₁ κ₁ ℓ S n st ∧
          ∀ R : ℝ, 1 < R → R ≤ n → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ρ / (4 * R) →
            ECand d₁ ℓ 1 st R ε' →
            MixedCandidate (N k) L (W k) (ν k) (B k) Mc d₁ ρ gain ε
              r T C lev γ j u Q A H

/-- A fine stage grid together with its prepared model. -/
def StageReady (d₁ κ₁ ℓ S η ρ : ℝ) (n : ℕ) : Prop :=
  ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ),
    FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧ δ₀ ≤ ρ * gain ∧
      StageModel d₁ κ₁ ℓ S η ρ n m s gain δ₀

/-- The conclusion of `PreparationStatement` for one choice of parameters. -/
def DiscoveryOn (d₁ κ₁ ℓ S η ρ : ℝ) : Prop :=
  ∃ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ),
    FineGrid m s gain ρ ∧ 0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ₀ ∧
    δ₀ ≤ ρ * gain ∧ Discovery d₁ κ₁ ℓ S η ρ m s gain δ₀

/-- If discovery fails, every stage has a prepared model index without candidates. -/
theorem stageModel_without_candidates {d₁ κ₁ ℓ S η ρ : ℝ}
    (hcon : ¬ DiscoveryOn d₁ κ₁ ℓ S η ρ) (n : ℕ) (hready : StageReady d₁ κ₁ ℓ S η ρ n) :
    ∃ st : EStage (ℕ × (Fin 6 → ℝ)), StageGood d₁ κ₁ ℓ S n st ∧
      ∀ R : ℝ, 1 < R → R ≤ n → ∀ ε' : ℝ, 0 < ε' → ε' ≤ ρ / (4 * R) →
        ¬ ECand d₁ ℓ 1 st R ε' := by
  obtain ⟨m, s, gain, δ₀, hgrid, hg, hg', hδ, hδ', hP⟩ := hready
  by_contra hall
  push Not at hall
  apply hcon
  refine ⟨m, s, gain, δ₀, hgrid, hg, hg', hδ, hδ', ?_⟩
  intro N K L d W ω ν E P B f g G hX hprof Mp Dp
  obtain ⟨Mc, h1⟩ := hP N K L d W ω ν E P B f g G hX hprof Mp Dp
  refine ⟨Mc, fun ε hε => ?_⟩
  obtain ⟨σ, hσ, k₀, h2⟩ := h1 ε hε
  refine ⟨σ, hσ, k₀, fun k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hHm => ?_⟩
  obtain ⟨st, hgood, hret⟩ :=
    h2 k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hHm
  obtain ⟨R', hR1, hRn, ε', hε', hεR, hc⟩ := hall st hgood
  exact hret R' hR1 hRn ε' hε' hεR hc

/-- **The stage diagonal.** The frozen general candidate principle and a prepared model at every
stage give discovery on a fine grid. -/
theorem discoveryOn_of_stageReady (hE : CandidatePrinciple false (fun _ => True))
    {d₁ κ₁ ℓ S η ρ : ℝ} (hd₁ : 0 ≤ d₁) (hd₁' : d₁ < 1) (hκ₁ : 0 < κ₁) (hκ₁' : κ₁ ≤ 1)
    (hℓ : 0 < ℓ) (hS : 0 < S) (hS1 : S ≤ 1) (hρ : 0 < ρ)
    (hready : ∀ n : ℕ, StageReady d₁ κ₁ ℓ S η ρ n) :
    DiscoveryOn d₁ κ₁ ℓ S η ρ := by
  by_contra hcon
  choose st hgood hnone using fun n => stageModel_without_candidates hcon n (hready n)
  have hN2 : ∀ n, 2 ≤ (st n).N := fun n => by
    have := (hgood n).1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hNt : Filter.Tendsto (fun n => (st n).N) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n => (hgood n).1) ?_
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hK : (∀ n, 1 ≤ (st n).K) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, (st n).K ≤ (st n).N ^ ε := by
    refine ⟨fun n => (hgood n).2.1.1, fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / ε)
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    have h1N : 1 ≤ (st n).N := le_trans (by norm_num) (hN2 n)
    refine le_trans (hgood n).2.1.2 (Real.rpow_le_rpow_of_exponent_le h1N ?_)
    have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hpos]
    have : 1 / ε < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  have hlate : ∀ R : ℝ, ∀ᶠ n : ℕ in Filter.atTop, R ≤ (n : ℝ) := fun R => by
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge R
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    exact le_trans hn₀ (by exact_mod_cast hn)
  have h2 : ∀ R : ℝ, 1 < R → ∀ᶠ n in Filter.atTop, EH2 d₁ S (st n) R := fun R hR => by
    filter_upwards [hlate R] with n hn
    exact ((hgood n).2.2.2 R hR hn).1
  have h3 : ∀ R : ℝ, 1 < R → ∀ᶠ n in Filter.atTop, EH3 d₁ κ₁ ℓ 1 1 (st n) R := fun R hR => by
    filter_upwards [hlate R] with n hn
    exact ((hgood n).2.2.2 R hR hn).2.1
  have h4 : ∀ R : ℝ, 1 < R → ∀ᶠ n in Filter.atTop, EH4 1 (st n) R := fun R hR => by
    filter_upwards [hlate R] with n hn
    exact ((hgood n).2.2.2 R hR hn).2.2
  obtain ⟨R, hR, hc⟩ := candidates_of_stages hE st d₁ κ₁ ℓ S 1 1 hd₁ hd₁' hκ₁ hκ₁' hℓ hS hS1
    one_pos one_pos hN2 hNt hK (fun n => (hgood n).2.2.1) h2 h3 h4
  have hε : 0 < ρ / (4 * R) := by
    have : (0 : ℝ) < R := by linarith
    positivity
  obtain ⟨n, hcn, hn⟩ := ((hc _ hε).and_eventually (hlate R)).exists
  exact hnone n R hR hn _ hε le_rfl hcn

/-- The per-stage models for all parameters (no principle involved). -/
def StageModels : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, StageReady d₁ κ₁ ℓ S η ρ n

/-- Child (1) of the split of o199 from the per-stage models. -/
theorem preparationStatement_of_stageModels (h : StageModels) : PreparationStatement :=
  fun hE d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS1 hη hρ hρ' =>
    discoveryOn_of_stageReady hE hd hd' hκ hκ' hℓ hS hS1 hρ
      (h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS1 hη hρ hρ')

end

end Submission.Obl.k4_finite_path_candidate_conversion
