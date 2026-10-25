-- `prob_scalarData` and `prob_temperedLaw'` follow `prob_temperedLaw` of this LOT tree, o117,
-- session x0441, Submission/Obl/k4_quadratic_candidate_atlas_conversion/Assembly.lean.
-- `prob_menu_upper_tails` adapts `prob_fixed_depth_upper_tails` of o209 (accepted),
-- Submission/Obl/k4_fixed_menu_density_pruning/Outer.lean, to a tolerance per menu entry.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCore
import Submission.Obl.k4_fixed_menu_density_pruning.Outer
import Submission.Obl.k4_original_observation_atlas_encoding.Source

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Filter Set
open Submission.Lib.K4XInterface
open Submission.Obl.k4_fixed_menu_density_pruning (upperTail finite_common_power_tail)

/-- Graph atlases stay graph atlases for larger complexity and degree budgets. -/
theorem graphAtlas_mono {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {r₀ h θ β : ℝ} {M D M' D' T C : ℕ}
    {γ : Fin C → Fin W} {j : Fin C → Fin (2 ^ T)}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {P : Fin C → MvPolynomial (Fin 4) ℝ} {scale : Fin C → ℝ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))}
    {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)}
    (hN : 1 ≤ Nk) (hM : M ≤ M') (hD : D ≤ D')
    (hg : GraphAtlas Nk L W ω ν E B r₀ h θ β M D T C γ j c u Q P scale A F lst) :
    GraphAtlas Nk L W ω ν E B r₀ h θ β M' D' T C γ j c u Q P scale A F lst := by
  have hp : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hN hM
  obtain ⟨hC, hB, hdisj, hlst, hmeas, hcharts, hmass⟩ := hg
  refine ⟨hC.trans hp, fun w => ⟨(hB w).1, (hB w).2.1.trans hp, (hB w).2.2.trans hp⟩,
    hdisj, hlst, hmeas, fun b => ?_, hmass⟩
  obtain ⟨hdet, hcu, hQQ, hQ, hdeg, hcoef, hs0, hs1, hs2, hAm, hFm, hfmt, hA, hF, hroot⟩ :=
    hcharts b
  refine ⟨hdet, hcu.trans hp, hQQ.trans hp, hQ, hdeg, fun e => (hcoef e).trans hp, hs0,
    hs1.trans hp, hs2.trans hp, hAm, hFm, fun i => ⟨gfmt_mono hp hD (hfmt i).1,
      gfmt_mono hp hD (hfmt i).2⟩, fun l hl => ?_, hF, hroot⟩
  obtain ⟨h1, h2, h3⟩ := hA l hl
  exact ⟨h1.trans hp, fun e => (h2 e).trans hp, h3⟩

section ProbFacts

variable {N K : ℕ → ℝ} {L d S η : ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ))}
    {E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}

/-- The scalar data of every sample of the frozen problem, with one exponent pair. -/
theorem prob_scalarData (h : prob N K L d S η W ω ν E P B f g G) :
    ∃ M D : ℕ, ∀ k, ScalarData (N k) M D (W k) (ω k) (ν k) (E k) (B k) ∧
      Submission.Obl.k4_original_observation_atlas_encoding.temperedLaw (N k) M D (W k)
        (ω k) (ν k) (B k) ∧
      (∀ w, E k w ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hdata⟩
  rcases hdata.1 with ⟨M, D, hall⟩
  refine ⟨M, D, fun k => ?_⟩
  rcases hall k with ⟨hW, hω, hsum, hworlds, _⟩
  refine ⟨⟨hW, hω, hsum, fun w => ?_⟩, ⟨hW, hω, hsum, fun w => ?_⟩, fun w => ?_⟩
  · obtain ⟨hν, hB, hBup, hBinv, _, _, _, hE, _, _, hfmt, _, _⟩ := hworlds w
    exact ⟨hν, hB, hBup, hBinv, hE, hfmt⟩
  · obtain ⟨hν, hB, hBup, hBinv, _, _, hprior, _⟩ := hworlds w
    exact ⟨hν, hB, hBup, hBinv, hprior⟩
  · exact (hworlds w).2.2.2.2.2.2.2.2.1

/-- The frozen problem's upper pure-density tails, at every entry of a finite menu of fixed
depths and positive tolerances, have a common positive decay power. -/
theorem prob_menu_upper_tails {ι : Type*} [Fintype ι]
    (hp : prob N K L d S η W ω ν E P B f g G)
    (q τ : ι → ℝ) (hq : ∀ i, q i ∈ Icc 0 L) (hτ : ∀ i, 0 < τ i) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ i,
      upperTail (N k) (W k) (ω k) (ν k) (E k) (B k) f (g k) (τ i) (q i) ≤
        ENNReal.ofReal (N k ^ (-c)) := by
  rcases hp with ⟨hN, _, _, _, _, _, _, _, _, _, _, _, htail, _⟩
  apply finite_common_power_tail N (fun k => le_trans (by norm_num) (hN k))
  intro i
  obtain ⟨c, hc, ht⟩ := htail (q i) (τ i) (hq i).1 (hq i).2 (hτ i)
  refine ⟨c, hc, ht.mono ?_⟩
  intro k hk
  refine le_trans ?_ hk
  unfold upperTail
  apply Finset.sum_le_sum
  intro w _
  exact mul_le_mul' le_rfl (measure_mono (fun _ hp => Or.inr hp))

end ProbFacts

end Submission.Obl.k4_finite_positive_mixed_cover_realization
