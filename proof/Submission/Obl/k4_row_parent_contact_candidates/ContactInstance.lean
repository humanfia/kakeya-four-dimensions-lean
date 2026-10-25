/-
Adapted from: here:o222, session x0776, commit 0a43f16b.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ContactInstance.lean.
The contact-renewal helpers are reused under this obligation's namespace.
-/
import Mathlib
import Submission.Obl.k4_row_parent_contact_candidates.Pullback
import Submission.Obl.k4_row_parent_contact_candidates.ParentTower

/-!
# The zoomed contact instance

Inputs at one index: an original index `k`, a parent `Q` at the fixed depth
`r`, a row normalization `(B, λ)`, a retained incidence set `G` inside the
parent box, a grid of `M` deeper depths `r + (j+1) δ`, a pruning threshold `θ`
and a native polynomial `Pn` for the zoomed chart.

The zoomed instance uses the conditioned prior, the zoomed restrictions of the
original laws to the pruned set, the normalized trajectory coefficients, and at
every depth `σ` the retained descendants of the grid level of `σ`, with their
time blocks rebased in the unit block, their box constants transformed by
`zoomBox` and their tests pushed by `nPush`.
-/

namespace Submission.Obl.k4_row_parent_contact_candidates

open MeasureTheory Set Filter
open scoped ENNReal
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Inputs of the zoomed contact instance at one index. -/
structure ZoomInput (p : Parameters) (a : PreparedModel α) (r : ℝ) where
  /-- original index -/
  k : ℕ
  /-- parent label -/
  Q : Fin (a.n k r)
  /-- constant row -/
  B : Fin 2 → ℝ
  /-- skew -/
  lam : ℝ
  /-- retained incidences (contact set) -/
  G : Set (α × ℝ)
  /-- number of grid levels -/
  M : ℕ
  /-- grid step -/
  δ : ℝ
  /-- pruning threshold -/
  θ : ℝ
  /-- native polynomial of the zoomed chart -/
  Pn : MvPolynomial (Fin 4) ℝ

namespace ZoomInput

variable {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ZoomInput p a r)

/-- Grid depths below the parent. -/
def depth (j : Fin I.M) : ℝ := r + ((j : ℝ) + 1) * I.δ

/-- The parent zoom. -/
def Z : Zoom := parentZoom p a I.k r I.Q

/-- Tower labels below the parent. -/
abbrev Label := TowerLabel a I.k r I.Q I.depth

/-- Level of a tower label. -/
abbrev lv : I.Label → ℕ := towerLv
/-- Box of a tower label. -/
abbrev box : I.Label → Set (α × ℝ) := towerBox
/-- Weight of a tower label. -/
abbrev wt : I.Label → ℝ≥0∞ := towerWeight
/-- Ancestor relation of tower labels. -/
abbrev anc : I.Label → I.Label → Prop := towerAnc

/-- The removed set. -/
def removed : Set (α × ℝ) := towerRemoved (a.mu I.k) I.G I.lv I.box I.wt I.θ

/-- The pruned set. -/
def keep : Set (α × ℝ) := towerKeep (a.mu I.k) I.G I.lv I.box I.wt I.θ

/-- Retained descendants at one grid level. -/
def Ret (j : Fin I.M) : Type :=
  {i : {i : Fin (a.n I.k (I.depth j)) // i ∈ descSet (a.A I.k (I.depth j)) (a.j I.k (I.depth j))
      (a.A I.k r I.Q) (a.T I.k r) (a.j I.k r I.Q)} //
    towerRetained (a.mu I.k) I.G I.lv I.box I.wt I.θ I.anc (⟨j, i⟩ : I.Label)}

scoped instance (j : Fin I.M) : Fintype (I.Ret j) := by
  unfold Ret; classical infer_instance

/-- The grid level of a depth `σ` (requires `M ≥ 1`). -/
def lev (hM : 0 < I.M) (σ : ℝ) : Fin I.M :=
  ⟨min (I.M - 1) (⌊σ / I.δ⌋₊ - 1), by omega⟩

/-- The parent weight. -/
def W : ℝ≥0∞ := ENNReal.ofReal (a.q I.k r) * a.nu I.k (a.A I.k r I.Q)

/-- The time block of a retained descendant lies in the parent block. -/
theorem block_sub {j : Fin I.M} (x : I.Ret j) :
    interval (a.T I.k (I.depth j)) (a.j I.k (I.depth j) x.1.1) ⊆
      interval (a.T I.k r) (a.j I.k r I.Q) :=
  (mem_descSet.mp x.1.2).2

/-- The prior set of a retained descendant lies in the parent prior set. -/
theorem prior_sub {j : Fin I.M} (x : I.Ret j) :
    a.A I.k (I.depth j) x.1.1 ⊆ a.A I.k r I.Q :=
  (mem_descSet.mp x.1.2).1

end ZoomInput

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

/-- **The zoomed contact instance** along a sequence of inputs. -/
def zoomModel {p : Parameters} {a : PreparedModel α} {r : ℝ} (I : ℕ → ZoomInput p a r)
    (hM : ∀ m, 0 < (I m).M) : PreparedModel α where
  nu m := condPrior (a.nu (I m).k) (a.A (I m).k r (I m).Q)
  mu m := zoomLaw (a.mu (I m).k) (I m).keep (I m).Z.t₀ (I m).Z.q (I m).W
  rho m := zoomLaw (a.rho (I m).k) (I m).keep (I m).Z.t₀ (I m).Z.q (I m).W
  pi m := a.pi (I m).k
  b m l := Zoom.nCoeff (I m).Z (I m).B (I m).lam (a.b (I m).k l)
  P m := (I m).Pn
  T m σ := a.T (I m).k ((I m).depth ((I m).lev (hM m) σ)) - a.T (I m).k r
  n m σ := Fintype.card ((I m).Ret ((I m).lev (hM m) σ))
  j m σ i := relFin ((I m).block_sub ((Fintype.equivFin _).symm i))
  A m σ i := a.A (I m).k ((I m).depth ((I m).lev (hM m) σ)) ((Fintype.equivFin _).symm i).1.1
  B m σ i := a.B (I m).k ((I m).depth ((I m).lev (hM m) σ)) ((Fintype.equivFin _).symm i).1.1
  c m σ i := Zoom.zoomBox (I m).Z (I m).B (I m).lam
    (a.c (I m).k ((I m).depth ((I m).lev (hM m) σ)) ((Fintype.equivFin _).symm i).1.1)
  F m σ i := Zoom.nPush (I m).Z (I m).B (I m).lam
    (a.F (I m).k ((I m).depth ((I m).lev (hM m) σ)) ((Fintype.equivFin _).symm i).1.1)

end

end Submission.Obl.k4_row_parent_contact_candidates
