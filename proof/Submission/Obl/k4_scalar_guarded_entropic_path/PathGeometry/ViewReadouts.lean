import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewAt
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootRowSupport

/-! The actual row readouts of every numbered candidate parent, on the
same final space. Their histories use the exact suffix chain. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open TrueLiftChains PathMeasures

noncomputable section

namespace OriginalView

/-- A concrete row decoder and its literal nesting certificates. -/
structure Readouts {root final : Code} {D S η : ℝ}
    (a : OriginalView root final D S η) where
  row : (k : ℕ) → (j : Fin a.count) → Fin (W final k) → Fin (a.geometry k j).count
  world : ∀ k j g, (a.geometry k j).world (row k j g) = a.suffixChain.world k g
  history : ∀ k j g, (row k j g).val = a.suffixChain.history k (j.val + 1) g
  selected : ∀ k z, z ∈ a.suffixChain.pathSet k → ∀ j,
    (a.suffixChain.pullback k z).2 ∈ (a.geometry k j).selected (row k j z.1)
  projection : ∀ k (c f : Fin a.count), c ≤ f →
    ∃ π : ChartGeometry.RowProjection (a.geometry k c) (a.geometry k f),
      ∀ g, π.row (row k f g) = row k c g

theorem Readouts.row_eq_of_history_eq {root final : Code} {D S η : ℝ}
    {a : OriginalView root final D S η} (read : a.Readouts) (k : ℕ) (j : Fin a.count)
    (g g' : Fin (W final k))
    (h : a.suffixChain.history k (j.val + 1) g = a.suffixChain.history k (j.val + 1) g') :
    read.row k j g = read.row k j g' := by
  apply Fin.ext
  simpa only [read.history] using h

end OriginalView

namespace PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ} {root : Code}

def originalViewReadouts (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) :
    (path.originalView i certs hl before).Readouts where
  row := path.rootRow i certs
  world := path.rootRow_world i certs
  history := path.rootRow_history i certs
  selected := path.rootRow_selected i certs
  projection k c f hcf := by
    obtain ⟨π, hπ, _⟩ := path.root_rowProjection_with_rootRow i certs k c f hcf
    exact ⟨π, hπ⟩

/-- Every numbered actual parent carries these readouts; they are not
an additional assumption on the finite-stage construction. -/
theorem viewAt_readouts_nonempty (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    Nonempty (path.viewAt i certs hl before n).Readouts := by
  induction path generalizing n with
  | nil => exact ⟨originalViewReadouts _ i certs hl before⟩
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => exact ⟨originalViewReadouts _ i certs hl before⟩
    | succ n => exact ih certs.2 hl.2 _ n

def viewAtReadouts (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n : ℕ) :
    (path.viewAt i certs hl before n).Readouts :=
  Classical.choice (path.viewAt_readouts_nonempty i certs hl before n)

/-- Local future histories in a candidate are exactly the original
numbered future worlds in the full path, including the constant extension. -/
theorem viewAt_history_shift (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k t : ℕ)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    (path.viewAt i certs hl before n).suffixChain.history k t g =
      (path.measuredChain i certs).history k (n + t) g := by
  induction path generalizing n with
  | nil => rfl
  | cons r rs hstart hr node tail ih =>
    cases n with
    | zero => simp only [Nat.zero_add]; rfl
    | succ n =>
      rw [Nat.succ_add]
      change (tail.viewAt i certs.2 hl.2 _ n).suffixChain.history k t g =
        (tail.measuredChain i certs.2).history k (n + t) g
      exact ih certs.2 hl.2 _ n g

theorem viewAt_local_history_eq_future_world (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k t : ℕ)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    (path.viewAt i certs hl before n).suffixChain.history k t g =
      ((path.viewAt i certs hl before (n + t)).suffixChain.world k g).val :=
  (path.viewAt_history_shift i certs hl before n k t g).trans
    (path.viewAt_history i certs hl before (n + t) k g).symm

/-- Thus the actual world of view n+t determines every row at local
prefix t-1, without imposing a new finite partition. -/
theorem viewAtReadouts_row_val (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (before : Chain root (source.problem i)) (n k : ℕ)
    (j : Fin (path.viewAt i certs hl before n).count)
    (g : Fin (W (path.forget.finalFamily.problem i) k)) :
    ((path.viewAtReadouts i certs hl before n).row k j g).val =
      ((path.viewAt i certs hl before (n + j.val + 1)).suffixChain.world k g).val := by
  rw [OriginalView.Readouts.history, path.viewAt_history_shift i certs hl before n k,
    path.viewAt_history i certs hl before (n + j.val + 1) k]
  simp only [Nat.add_assoc]

end PathNodes.TrueGridPath

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
