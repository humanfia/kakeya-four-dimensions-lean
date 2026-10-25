-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/GreedyCoverage.lean.

import Submission.Obl.k4_quadratic_finite_greedy_cover.RoundedCoverage
import Submission.Obl.k4_quadratic_finite_greedy_cover.CoverageNumerics
import Submission.Obl.k4_quadratic_finite_greedy_cover.Monotonicity
import Submission.Obl.k4_quadratic_finite_greedy_cover.PathPriority
import Submission.Obl.k4_quadratic_finite_greedy_cover.PathFacts

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open MeasureTheory Set
open scoped ENNReal

/-- Residual discovery supplies the complete rounded finite candidate cover,
with complexity chosen before the requested subpower slack. -/
theorem greedy_coverage :
∀ d₁ κ₁ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < S → 0 < η → 0 < ρ → d₁ + ρ < 1 →
    ∀ (m : ℕ) (s : ℕ → ℝ) (gain δ₀ : ℝ), (0 < m ∧ 0 < s 0 ∧ (∀ i, i + 1 < m → s i < s (i + 1)) ∧ s (m - 1) = 1) → 0 < gain → gain ≤ 1 / 8 →
    0 < δ₀ → δ₀ ≤ ρ * gain → discovery d₁ κ₁ S η ρ m s gain δ₀ →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
    (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
    ∀ Mp Dp : ℕ, ∃ Mg Dg : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ σ : ℝ, 0 < σ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ r T nw κ C lev par γ j c u Q R A F lst,  path (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst →
      width (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mg Dg ε ∨ RoundedCoverage (N k) L (W k) (ω k) (ν k) (B k) d₁ ρ gain m r T C lev γ j A F Mg Dg ε := by
  intro d₁ κ₁ S η ρ hd₁ hd₁' hκ₁ hκ₁' hS hη hρ hdρ
  intro m s gain δ₀ hshape hgain hgain' hδ₀ hδ₀' hdiscovery
  intro N K L d W ω ν E P B f g G hprob hlinear Mp Dp
  obtain ⟨hN₂, hNt, hL, hω, hωsum, hν, hB, hE⟩ :=
    prob_basic N K L d S η W ω ν E P B f g G hprob
  have hN (k : ℕ) : 1 ≤ N k := by linarith [hN₂ k]
  have hstep : 0 < ρ * gain := mul_pos hρ hgain
  obtain ⟨Mc, Dc, hdisc⟩ := hdiscovery N K L d W ω ν E P B f g G hprob hlinear Mp Dp
  let a := (d₁ / 8 + ρ * gain) * L
  let Mg := max Mc ⌈2 * (Mp : ℝ) + a + 3⌉₊
  let Dg := max Dc (max Dp 4)
  have ha : 0 ≤ a := mul_nonneg (add_nonneg (div_nonneg hd₁ (by norm_num)) hstep.le) hL.le
  have hMg : 2 * (Mp : ℝ) + a + 3 ≤ (Mg : ℝ) :=
    (Nat.le_ceil _).trans (by dsimp [Mg]; exact_mod_cast Nat.le_max_right Mc ⌈2 * (Mp : ℝ) + a + 3⌉₊)
  refine ⟨Mg, Dg, ?_⟩
  intro ε hε hε'
  let εin := ε / 8
  have hεin : 0 < εin := by dsimp [εin]; positivity
  have hεinε : εin ≤ ε := by dsimp [εin]; linarith
  have hεinone : εin ≤ 1 := hεinε.trans hε'
  obtain ⟨σd, hσd, kd, hdiscd⟩ := hdisc εin hεin
  let menu := ⌈(1 / 8 : ℝ) / (ρ * gain)⌉₊ + 1
  let D := ((m * menu : ℕ) : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast Nat.mul_pos hshape.1 (by dsimp [menu]; omega : 0 < menu)
  obtain ⟨σb, hσb, hbudget⟩ := eventual_coverage_budget N hN hNt (ρ * gain * L) ε D
    (mul_pos hstep hL) hε hD
  let σ := min σd σb
  obtain ⟨kb, hkb⟩ := Filter.eventually_atTop.mp
    (hbudget.and (hNt.eventually_ge_atTop (194 : ℝ)))
  refine ⟨σ, lt_min hσd hσb, max kd kb, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp
  have hkd : kd ≤ k := (Nat.le_max_left _ _).trans hk
  have hkbk : kb ≤ k := (Nat.le_max_right _ _).trans hk
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hp.1
  have hκbudget : κ ≤ N k ^ σb := hp.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_right _ _))
  have hb := (hkb k hkbk).1 κ εin hκpos hκbudget hεin.le
  have hpdisc := path_slack_mono (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
    Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst σd (hN k) (min_le_left _ _) hp
  have hdiscH := hdiscd k hkd r T nw κ C lev par γ j c u Q R A F lst hpdisc
  rcases path_priority_cover (N k) L (W k) (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀
    Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst Mc d₁ ρ gain εin
    (width (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain Mc Dc εin)
    (hN k) hL.le hd₁ (hω k) (hν k) (hE k) hshape.1 hp hdiscH with
    hw | ⟨H₀, hH₀, hHmass, U₀, hU₀, hpriority, hrep, hcov⟩
  · exact Or.inl (width_mono (N k) L (W k) (ω k) (ν k) (E k) (B k) m r T nw gain
      Mc Dc Mg Dg εin ε (hN k) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
      hεinε (fun w => (hB k w).le) hw)
  have (w : Fin (W k)) : IsProbabilityMeasure (ν k w) := hν k w
  have hpcopy := hp
  rcases hpcopy with ⟨hκ, hκN, hC, hend, hlevels, hlists, hold, hnodes⟩
  have hFmeas (b : Fin C) : MeasurableSet (F b) := by
    rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, hF, _⟩
    exact hF
  have hFsub (b : Fin C) : F b ⊆ E k (γ b) := by
    rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, _, _, _, hF, _⟩
    exact fun p hp => (hF p hp).1
  have hHm (w : Fin (W k)) : MeasurableSet (terminalUnion m lev γ F w) :=
    terminalUnion_measurable (W k) C m lev γ F hFmeas w
  have hHfin (w : Fin (W k)) : (ν k w).prod volume (terminalUnion m lev γ F w) ≠ ∞ :=
    measure_ne_top_of_subset ((terminalUnion_subset (W k) C m lev γ F (E k) hFsub w).trans (hE k w))
      (by simp)
  have henv (a : CandidateDatum C) (ha : a ∈ U₀) :
      a.trajectories ⊆ candidateEnvelope (N k) L (W k) C (B k) ρ gain εin r T lev γ j A a := by
    obtain ⟨P, hP, hh⟩ := hrep a ha
    rw [hh]
    exact sdiff_subset
  obtain ⟨i, hi, z, hz, U, hUeq, hUne, hUi, hmass⟩ :=
    candidate_level_gain_counted_mass (N k) L (W k) C Mc m (ν k) (ω k) (B k)
      ρ gain εin (κ⁻¹ / 2) r T lev γ j A H₀ (terminalUnion m lev γ F) U₀
      hshape.1 hgain.le hstep (by positivity) (hν k) (hω k) (hωsum k) (hB k) hb.1
      (fun b => (hnodes b).1) (fun b => (hnodes b).2.1)
      (fun w => (hH₀ w).2.1) hHfin (fun a ha => (hU₀ a ha).1) henv hpriority hold hcov
  have hUS : U ⊆ U₀ := by rw [hUeq]; exact Finset.filter_subset _ _
  obtain ⟨hAprodpos, hAprodfin⟩ := path_packetRegion_budget (N k) L (W k) (ω k) (ν k) (E k)
    (B k) f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst (hN k) (hν k) hp
  have hApos (b : Fin C) : 0 < (ν k (γ b)).real (A b) := by
    have hh := hAprodpos b
    rw [measureReal_def, packetRegion_measure, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2 : ℝ) ^ T (lev b))] at hh
    exact pos_of_mul_pos_left hh (by positivity)
  have hAfmt (b : Fin C) (copy : ℕ) : fmt 6 (N k ^ Mp) Dp {v | (copy, v) ∈ A b} := by
    rcases (hnodes b).2.2 with ⟨_, _, _, _, _, _, _, _, hfmt, _⟩
    exact (hfmt copy).1
  have hcount := priority_family_card_bound (N k) L (W k) C Mc (ν k) (B k) d₁ ρ gain εin
    r T lev γ j A H₀ U₀ (hN k) hL.le hd₁ hApos (fun b => by finiteness) hU₀ hpriority
  have hcomplex := priority_polynomial_complexity (N k) a εin (C : ℝ) (U₀.card : ℝ) Mp Mg
    (hkb k hkbk).2 ha hεinone hC hcount hMg
  have hmass' : N k ^ (-ε) ≤ ∑ a ∈ U, ω k (γ a.parent) * ((ν k (γ a.parent)).prod volume).real
      (countedPacket (terminalUnion m lev γ F (γ a.parent)) a.trajectories a.test
        (B k (γ a.parent) / (N k ^ (ρ * gain * L + εin)) ^ 4) (T i) (j a.parent)) := by
    exact hb.2.2.trans hmass
  exact Or.inr (roundedCoverage_of_priority_subfamily (N k) L (W k) C Mc Mp Dp Mg Dg m
    (ν k) (ω k) (B k) d₁ ρ gain εin ε r T lev γ j A F H₀ U₀ U i z
    (hN k) hL.le hd₁ hd₁'.le hstep hεin.le hεinε hb.2.1 hb.1
    (hν k) (hω k) (hB k) hApos hAfmt (fun w => (hH₀ w).2.1) hHm hHfin hU₀ hpriority hrep hold
    hi hUS hUne (fun a ha => (hUi a ha).1)
    (fun a ha => ⟨(hUi a ha).2.2.1, (hUi a ha).2.2.2.le⟩)
    (Nat.le_max_right _ _) (Nat.le_max_left _ _) hcomplex.1 hcomplex.2 hmass')

end Submission.Obl.k4_quadratic_finite_greedy_cover
