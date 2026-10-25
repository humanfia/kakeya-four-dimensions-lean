-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/FiniteInterceptSelection.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/FiniteInterceptSelection.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.TraversalMass
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.HeavyIntercept

/-! Selection of a heavy original intercept from a finite retained traversal experiment. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Sf Sc Ar Iv Pal Tc Bin Cell : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc] [DecidableEq Bin] [DecidableEq Cell]

/-- Positive retained path mass, an endpoint cap, and a joint pair budget give
a heavy intercept in the original event law X.P. The experiment and its
terminal test may depend on the starting event. -/
theorem finite_traversal_heavy_intercept_of_positive_cap
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → Ω → List (Pal × Tc) → ℝ) (hG : ∀ s e l, 0 ≤ G s e l)
    (bin : Ω → Bin) (cell : Ω → Cell)
    (hfine : ∀ e er, X.fine e = X.fine er → bin e = bin er)
    (hline : ∀ er e', X.armKey false er = X.armKey false e' → bin er = bin e')
    (F : Finset (Bin × Cell)) (n : ℕ) (p B m : ℝ)
    (hp : 0 < p) (hB : 0 < B) (hm : 0 < m) (hcard : (F.card : ℝ) ≤ B)
    (hmass : m ≤ ∑ e, X.P e * finiteTraversalValue X prior lam (allowed e) (G e) n e [])
    (hsupport : ∀ s e l, 0 < G s e l → (bin e, cell e) ∈ F)
    (hcap : ∀ e t, 0 < X.P e → finiteTraversalValue X prior lam (allowed e)
      (fun x h => if cell x = t then G e x h else 0) n e [] ≤ p) :
    ∃ b : Bin, m / (2 * p * B) ≤ ∑ e ∈ univ.filter (fun e => bin e = b), X.P e := by
  let W : Ω → Ω → ℝ := fun e e' => finiteTraversalMatrix X prior lam (allowed e) (G e) n e e'
  have hW : ∀ e e', 0 ≤ W e e' := fun e =>
    finiteTraversalMatrix_nonneg X hP prior lam (allowed e) (G e) (hG e) n e
  have hmassW : m ≤ ∑ e, ∑ e', W e e' := by
    have heq : (∑ e, ∑ e', W e e') =
        ∑ e, X.P e * finiteTraversalValue X prior lam (allowed e) (G e) n e [] := by
      apply sum_congr rfl
      intro e _
      simp only [W, finiteTraversalMatrix, ← mul_sum, finiteTraversalValue_endpoint_sum,
        mem_univ, ite_true]
    rw [heq]
    exact hmass
  have hsupportW : ∀ e e', 0 < W e e' → (bin e, cell e') ∈ F := by
    intro e e' hpos
    have hbin : bin e = bin e' :=
      finiteTraversalMatrix_bin_eq_of_pos X prior lam (allowed e) bin hfine hline (G e) n e e' hpos
    have hpair : (bin e', cell e') ∈ F := by
      by_contra hn
      have hterminal : (fun x h => if x = e' then G e x h else 0) = 0 := by
        funext x h
        by_cases hx : x = e'
        · subst x
          have hz : G e e' h = 0 := by
            apply le_antisymm _ (hG e e' h)
            by_contra hnot
            exact hn (hsupport e e' h (lt_of_not_ge hnot))
          simp [hz]
        · simp [hx]
      have hz : W e e' = 0 := by
        dsimp [W, finiteTraversalMatrix]
        rw [hterminal, ← finiteTraversalTerminalForm_apply]
        simp
      rw [hz] at hpos
      exact (lt_irrefl _ hpos).elim
    rwa [hbin]
  have hcapW (e : Ω) (t : Cell) :
      (∑ e' ∈ univ.filter (fun e' => cell e' = t), W e e') ≤ p * X.P e := by
    change (∑ e' ∈ univ.filter (fun e' => cell e' = t),
      finiteTraversalMatrix X prior lam (allowed e) (G e) n e e') ≤ p * X.P e
    rw [finiteTraversalMatrix_cell_sum]
    rcases (hP e).eq_or_lt with hz | hpos
    · rw [← hz]
      simp
    · exact (mul_le_mul_of_nonneg_left (hcap e t hpos) (hP e)).trans_eq (mul_comm _ _)
  exact exists_heavy_intercept_of_path_cell_cap X.P W bin cell F p B m hp hB hm
    hW hcard hmassW hsupportW hcapW

theorem finite_traversal_heavy_intercept
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (G : Ω → Ω → List (Pal × Tc) → ℝ) (hG : ∀ s e l, 0 ≤ G s e l)
    (bin : Ω → Bin) (cell : Ω → Cell)
    (hfine : ∀ e er, X.fine e = X.fine er → bin e = bin er)
    (hline : ∀ er e', X.armKey false er = X.armKey false e' → bin er = bin e')
    (F : Finset (Bin × Cell)) (n : ℕ) (p B m : ℝ)
    (hp : 0 < p) (hB : 0 < B) (hm : 0 < m) (hcard : (F.card : ℝ) ≤ B)
    (hmass : m ≤ ∑ e, X.P e * finiteTraversalValue X prior lam (allowed e) (G e) n e [])
    (hsupport : ∀ s e l, 0 < G s e l → (bin e, cell e) ∈ F)
    (hcap : ∀ e t, finiteTraversalValue X prior lam (allowed e)
      (fun x h => if cell x = t then G e x h else 0) n e [] ≤ p) :
    ∃ b : Bin, m / (2 * p * B) ≤ ∑ e ∈ univ.filter (fun e => bin e = b), X.P e :=
  finite_traversal_heavy_intercept_of_positive_cap X hP prior lam allowed G hG bin cell
    hfine hline F n p B m hp hB hm hcard hmass hsupport (fun e t _ => hcap e t)

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
