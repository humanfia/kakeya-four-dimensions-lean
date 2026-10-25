import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathViews

/-! Nested histories are the actual original world labels along the
literal refinement path. They depend only on the final leaf world. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open TrueLiftChains PathMeasures

noncomputable section

namespace PathMeasures.RefinementChain

def world {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    Fin (W z k) → Fin (W p (chain.sample k)) :=
  match chain with
  | .nil _ => id
  | .cons w _ tail => w.world (tail.sample k) ∘ tail.world k

theorem pullback_world {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (u : Fin (W z k) × State) : (chain.pullback k u).1 = chain.world k u.1 := by
  induction chain with
  | nil => rfl
  | cons w hp tail ih =>
    change w.world (tail.sample k) (tail.pullback k u).1 =
      w.world (tail.sample k) (tail.world k u.1)
    rw [ih]

/-- Histories are extended constantly past the last genuine node, as
required by the all-natural-index entropy chain rule. -/
def history {p z : Code} (chain : RefinementChain p z) (k n : ℕ) : Fin (W z k) → ℕ :=
  match chain with
  | .nil _ => fun g => g.val
  | .cons w _ tail =>
      match n with
      | 0 => fun g => (w.world (tail.sample k) (tail.world k g)).val
      | n + 1 => tail.history k n

theorem history_zero {p z : Code} (chain : RefinementChain p z) (k : ℕ) (g : Fin (W z k)) :
    chain.history k 0 g = (chain.world k g).val := by
  cases chain <;> rfl

/-- Every later genuine world determines the preceding original world. -/
theorem history_nested {p z : Code} (chain : RefinementChain p z) (k n : ℕ)
    (g g' : Fin (W z k)) (h : chain.history k (n + 1) g = chain.history k (n + 1) g') :
    chain.history k n g = chain.history k n g' := by
  induction chain generalizing n with
  | nil => exact h
  | cons w hp tail ih =>
    cases n with
    | zero =>
      have hw : tail.world k g = tail.world k g' := by
        apply Fin.ext
        exact (tail.history_zero k g).symm.trans (h.trans (tail.history_zero k g'))
      change (w.world (tail.sample k) (tail.world k g)).val =
        (w.world (tail.sample k) (tail.world k g')).val
      rw [hw]
    | succ n => exact ih n g g' h

end PathMeasures.RefinementChain

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ} {root : Code}

/-- The world of each actual candidate view is exactly its node history,
with the sample maps and parent priors from the same chosen path. -/
theorem originalViews_get_history (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (k n : ℕ)
    (a : OriginalView root (path.forget.finalFamily.problem i) (ctx.D i) ctx.S₀ ctx.η)
    (ha : (path.originalViews i certs hl before)[n]? = some a)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    (path.measuredChain i certs).history k n g = (a.suffixChain.world k g).val := by
  induction path generalizing n with
  | nil =>
    cases n with
    | zero =>
      simp only [originalViews, List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      rfl
    | succ n => simp [originalViews] at ha
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero =>
      change some ((TrueGridPath.cons r rs hstart hr node tail).originalView i certs hl before) =
        some a at ha
      have heq := Option.some.inj ha
      clear ha
      subst a
      exact RefinementChain.history_zero _ _ _
    | succ n =>
      exact ih certs.2 hl.2 _ n a ha g

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
