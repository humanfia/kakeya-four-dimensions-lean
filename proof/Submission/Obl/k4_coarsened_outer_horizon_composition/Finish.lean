import Submission.Obl.k4_coarsened_outer_horizon_composition.Coarsening
import Submission.Obl.k4_coarsened_outer_horizon_composition.Horizon

/-! The remaining geometric input is own-depth label preparation. This module
completes the exact frozen composition from that input. The other helpers were
merged from this obligation's x0501 branch through 21e3679. -/

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set

set_option linter.unusedVariables false

theorem chart_extra_mono
    {Nk κ j r Bv : ℝ} {M D T : ℕ} {Ev F : Set Inc}
    {c u : E2} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {ex ex' : Prop}
    (he : ex → ex') (hc : chart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    chart Nk M D κ T j r Bv Ev c u Q R A F ex' := by
  rcases hc with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, he h12⟩

/-- Lists at a native depth can be keyed by any finer native observation. -/
theorem known_finer
    {N K : ℕ → ℝ} {W : ℕ → ℕ}
    {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Line}
    {E : (k : ℕ) → Fin (W k) → Set Inc}
    {B : (k : ℕ) → Fin (W k) → ℝ} {f : ℝ → ℝ}
    {r L a h : ℝ} (hN : ∀ k, 1 ≤ N k) (hrL : r ≤ L)
    (hk : known N K r W ω ν E B f a h) :
    known N K L W ω ν E B f a h := by
  rcases hk with ⟨M, D, hk⟩
  refine ⟨M, D, fun ε hε => (hk ε hε).mono ?_⟩
  intro k hk
  rcases hk with ⟨κ, hκ, hκN, T, C, γ, j, c, u, Q, R, A, F, lst,
    hT, hC, hdisj, hlist, hcharts, hmass⟩
  let q := Submission.Lib.K4Homogenization.coarsenObservation (X := E3) (N k) r L
  refine ⟨κ, hκ, hκN, T, C, γ, j, c, u, Q, R, A, F,
    (fun γ₁ o => lst γ₁ (q o)), hT, hC, hdisj,
    (fun γ₁ o => hlist γ₁ (q o)), ?_, hmass⟩
  intro b
  apply chart_extra_mono (hc := hcharts b)
  intro hb p hp
  change b ∈ lst (γ b) (q (obs (B k (γ b)) (δ (N k) L) p))
  have heq : obs (B k (γ b)) (δ (N k) r) p =
      q (obs (B k (γ b)) (δ (N k) L) p) :=
    congrFun (obs_factorization (hN k) hrL (B k (γ b))) p
  exact heq ▸ hb p hp

/-- The sole remaining input after complete angular coarsening: true terminal
systems admit bounded lists at their own native observation depth. -/
def OwnDepthPreparation : Prop :=
  ∀ N K L d S η W ω ν E P B f g G,
    prob N K L d S η W ω ν E P B f g G →
    ∀ h : ℝ, term N K L W ω ν E B f h →
      known N K L W ω ν E B f L h

/-- Complete the frozen o148 conclusion from own-depth label preparation. No
additional density, normalized-problem or attainable-infimum assumption is used. -/
theorem composition_of_own_depth
    (hinit : Initial) (htransfer : Transfer) (hprep : OwnDepthPreparation) :
    ∀ N K L d S η W ω ν E P B f g G,
      prob N K L d S η W ω ν E P B f g G →
      ∀ r q U : ℝ, 0 < r → r ≤ L → 0 < q → q < 1 →
        (∀ s : ℝ, 0 ≤ s → s ≤ r → f r - f s ≤ q * (r - s)) →
        0 ≤ U →
        (∀ N₂ K₂ L₂ d₂ W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂,
          prob N₂ K₂ L₂ d₂ S η W₂ ω₂ ν₂ E₂ P₂ B₂ f₂ g₂ G₂ →
          d₂ ≤ d → H N₂ K₂ L₂ W₂ ω₂ ν₂ E₂ B₂ f₂ ≤ U * L₂) →
        ∃ g₂ G₂, prob N K r q S η W ω ν E P B f g₂ G₂ ∧
          H N K L W ω ν E B f ≤ H N K r W ω ν E B f + U * (L - r) := by
  intro N K L d S η W ω ν E P B f g G hp r q U hr hrL hq hq1 hcap hU hbound
  obtain ⟨G₂, hp₂⟩ := coarsened_problem hp hr hrL hq hq1 hcap
  refine ⟨g, G₂, hp₂, ?_⟩
  by_cases heq : r = L
  · subst r
    simp
  · apply horizon_of_preparation htransfer hp hr.le (lt_of_le_of_ne hrL heq) hbound
    · exact ⟨r + 1, hinit N K r q S η W ω ν E P B f g G₂ hp₂
        (r + 1) (by linarith)⟩
    · intro h hh
      exact known_finer (fun k => by linarith [hp.1 k]) hrL
        (hprep N K r q S η W ω ν E P B f g G₂ hp₂ h hh)

end Submission.Obl.k4_coarsened_outer_horizon_composition
