/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/MatchingSequence.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.UniformSample
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.TestedSequence
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Filter Set
open NormalizationStep

/-- Local graph matching turns the normalized tested sequence into the exact
paired sequence, with a loss exponent uniform in every polynomial format. -/
theorem matching_of_tested (hmatch : Matching) (d₀ : ℝ) (hd₁ : d₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
      (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
      (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (B : (k : ℕ) → Fin (W k) → ℝ) (L dc a h : ℝ),
      0 < a → 0 < dc → dc ≤ d₀ → TestedSequence True 2 N W ω ν E B L dc a h →
        paired N W ω ν E B L (C * a) h := by
  classical
  by_cases hd₀ : 0 ≤ d₀
  · let d := (1 + d₀) / 2
    have hd0 : 0 ≤ d := by dsimp [d]; linarith
    have hd1 : d < 1 := by dsimp [d]; linarith
    have hdd : d₀ < d := by dsimp [d]; linarith
    obtain ⟨ε₀, hε₀, R₀, hR₀, hmb⟩ := matching_unnormalized hmatch d hd0 hd1
    obtain ⟨p, hp⟩ := matchingScales_at_middle hdd hd0 hd1 hε₀
    have hmbp : MatchBound p.middle ε₀ R₀ := hp.symm ▸ hmb
    let J := Classical.choice nonempty_jetData
    have hpout : 0 < p.output := by have := p.size_one; dsimp [MatchingScales.output]; linarith
    refine ⟨p.output, hpout, ?_⟩
    intro N W ω ν E B L dc a h ha hdc hdc₀ ht
    rcases ht with ⟨hN, hNt, hL, hω, hωsum, hν, hB, hE, M, D, hs⟩
    refine ⟨hN, hNt, hL, hω, hωsum, hν, hB, hE, M, D, ?_⟩
    intro ε hε
    let εin := min ε a
    have hεin : 0 < εin := lt_min hε ha
    let X₀ := max 8 (max (9 * gridConstant + 1)
      (max R₀ (max (3 * J.C₂) (max matchingVolumeConstant (matchingBadConstant p J)))))
    have hbig : ∀ᶠ k in atTop, X₀ ≤ N k ^ a :=
      Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow hNt ha X₀
    refine ((hs εin hεin).and_eventually hbig).mono ?_
    intro k hk
    obtain ⟨s⟩ := hk.1
    have hNk : 1 ≤ N k := by linarith [hN k]
    have hX : 8 ≤ N k ^ a := (le_max_left _ _).trans hk.2
    have hX₁ : max (9 * gridConstant + 1)
        (max R₀ (max (3 * J.C₂) (max matchingVolumeConstant (matchingBadConstant p J))))
        ≤ N k ^ a := (le_max_right _ _).trans hk.2
    have hgrid : 9 * gridConstant < N k ^ a := by
      have := (le_max_left _ _).trans hX₁
      linarith
    have hX₂ : max R₀ (max (3 * J.C₂) (max matchingVolumeConstant (matchingBadConstant p J)))
        ≤ N k ^ a := (le_max_right _ _).trans hX₁
    have hXR : R₀ ≤ N k ^ a := (le_max_left _ _).trans hX₂
    have hX₃ : max (3 * J.C₂) (max matchingVolumeConstant (matchingBadConstant p J))
        ≤ N k ^ a := (le_max_right _ _).trans hX₂
    have hXJ : 3 * J.C₂ ≤ N k ^ a := (le_max_left _ _).trans hX₃
    have hX₄ : max matchingVolumeConstant (matchingBadConstant p J) ≤ N k ^ a :=
      (le_max_right _ _).trans hX₃
    have hXV : matchingVolumeConstant ≤ N k ^ a := (le_max_left _ _).trans hX₄
    have hXB : matchingBadConstant p J ≤ N k ^ a := (le_max_right _ _).trans hX₄
    have hκX : s.κ ≤ N k ^ a := s.κ_le.trans
      (Real.rpow_le_rpow_of_exponent_le hNk (min_le_right ε a))
    change PairedAt (N k) (W k) (ω k) (ν k) (E k) (B k) L (p.output * a) h M D ε
    exact s.uniform_pairedAt p J hmbp hR₀ trivial (by norm_num) (hω k) (hωsum k)
      hNk ha hdc.le hdc₀ hX hgrid hXR hXJ hXV hXB hκX (min_le_left ε a)
  · refine ⟨1, by norm_num, ?_⟩
    intro N W ω ν E B L dc a h ha hdc hdc₀ ht
    exfalso
    linarith

/-- The matching child with the expanded existential test interface. -/
theorem matching_of_raw_tested (hmatch : Matching) (d₀ : ℝ) (hd₁ : d₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
      (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
      (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
      (B : (k : ℕ) → Fin (W k) → ℝ) (L dc a h : ℝ),
      0 < a → 0 < dc → dc ≤ d₀ → TestedSequenceRaw True 2 N W ω ν E B L dc a h →
        paired N W ω ν E B L (C * a) h := by
  obtain ⟨C, hC, h⟩ := matching_of_tested hmatch d₀ hd₁
  refine ⟨C, hC, ?_⟩
  intro N W ω ν E B L dc a h₀ ha hdc hdc₀ ht
  exact h N W ω ν E B L dc a h₀ ha hdc hdc₀
    ((testedSequence_iff_raw True 2 N W ω ν E B L dc a h₀).mpr ht)

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
