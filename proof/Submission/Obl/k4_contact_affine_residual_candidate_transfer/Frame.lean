import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Levels
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.HistoryCore
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Palettes
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ContactChart
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ShearedCells
import Submission.Lib.K4ContactNormalization.ResidualNormalization

/-!
# The residual frame at one index

At one index `k` the residual model is read off a finite frame:

* grid depths `depth h = s₀ + h * (U' / m)`, `h ≤ m`, of the original model;
* ancestor maps between consecutive grid depths (from the original nesting);
* affine palette entries at every grid depth, padded to a common count `M`;
* a parent true label `i₀` at depth `s₀` with a successful entry `u₀`;
* a measurable core of the original incidence law, on which simultaneous
  history floors hold (from `exists_finite_history_core`).

The labels of the residual model at grid level `h` are the retained history
nodes: original labels at `depth h` with an entry history, whose history
incidence meets the core. Coordinates are the contact chart of the parent block
followed by the affine residual normalization by the parent's entry.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

/-- The original depth of grid level `h`; levels beyond `m` stay at the last
grid depth, so that ancestor maps exist at every level. -/
def frameDepth (s₀ U' : ℝ) (m h : ℕ) : ℝ := s₀ + ((min h m : ℕ) : ℝ) * (U' / m)

/-- The finite choices at one index. -/
structure Frame {α : Type} [MeasurableSpace α] (D : Data α) (k : ℕ) (s₀ U' : ℝ) where
  /-- number of grid steps -/
  m : ℕ
  /-- common number of palette entries -/
  M : ℕ
  /-- palette fit constant -/
  H : ℝ
  /-- ancestors between consecutive grid depths -/
  anc : (h : ℕ) → Fin (D.n k (frameDepth s₀ U' m (h + 1))) →
    Fin (D.n k (frameDepth s₀ U' m h))
  /-- palette entries at each grid depth -/
  pal : (h : ℕ) → Fin (D.n k (frameDepth s₀ U' m h)) → Fin M → Fin 4 → ℝ
  /-- the parent true label -/
  i₀ : Fin (D.n k (frameDepth s₀ U' m 0))
  /-- the parent's successful entry -/
  u₀ : Fin M
  /-- the core of the original incidence law -/
  core : Set (α × ℝ)

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (fr : Frame D k s₀ U')

/-- The original depth of level `h`. -/
def depth (h : ℕ) : ℝ := frameDepth s₀ U' fr.m h

/-- The number of original labels at level `h`. -/
def nl (h : ℕ) : ℕ := D.n k (fr.depth h)

/-- The original block exponent at level `h`. -/
def Tl (h : ℕ) : ℕ := D.T k (fr.depth h)

/-- The original block of an original label. -/
def block (h : ℕ) (i : Fin (fr.nl h)) : Set ℝ := Data.I (fr.Tl h) (D.j k (fr.depth h) i)

/-- Left end of an original block. -/
def left (h : ℕ) (i : Fin (fr.nl h)) : ℝ :=
  ((D.j k (fr.depth h) i : ℕ) : ℝ) / (2 : ℝ) ^ fr.Tl h

/-- Right end of an original block. -/
def right (h : ℕ) (i : Fin (fr.nl h)) : ℝ :=
  (((D.j k (fr.depth h) i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ fr.Tl h

/-- The first-fit successful entry sets on the whole original block. -/
def entry (h : ℕ) (i : Fin (fr.nl h)) (u : Fin fr.M) : Set α :=
  assignedAffineEntry (D.b k) (D.B k (fr.depth h) i) (fr.pal h i)
    (fr.left h i) (fr.right h i) (fr.H * D.N k ^ (-fr.depth h)) u

/-- Entry histories along the original ancestor chains. -/
def hist (h : ℕ) (i : Fin (fr.nl h)) (u : EntryHistory fr.M h) : Set α :=
  historyAssignment fr.nl (fun h => D.A k (fr.depth h)) fr.entry fr.anc h i u

/-- The history incidence of a node. -/
def event (h : ℕ) (i : Fin (fr.nl h)) (u : EntryHistory fr.M h) : Set (α × ℝ) :=
  fr.hist h i u ×ˢ fr.block h i

/-- The nodes at level `h` that meet the core. -/
def retained (h : ℕ) : Finset (Fin (fr.nl h) × EntryHistory fr.M h) := by
  classical
  exact Finset.univ.filter fun a => (fr.event h a.1 a.2 ∩ fr.core).Nonempty

/-- The node of a residual label. -/
def node (h : ℕ) (i : Fin (fr.retained h).card) : Fin (fr.nl h) × EntryHistory fr.M h :=
  ((fr.retained h).equivFin.symm i).1

/-- The last entry of a history. -/
def lastEntry {M : ℕ} : (h : ℕ) → EntryHistory M h → Fin M
  | 0, u => u
  | _ + 1, u => u.2

/-! ### The parent chart -/

/-- Parent block exponent and parent block start. -/
def T₀ : ℕ := fr.Tl 0
def t₀ : ℝ := fr.left 0 fr.i₀
/-- Parent block length. -/
def q₀ : ℝ := ((2 : ℝ) ^ fr.T₀)⁻¹
/-- Parent row centers at the start of the parent block. -/
def Z₀ : ℝ := D.c k (fr.depth 0) fr.i₀ 0 + fr.t₀ * D.c k (fr.depth 0) fr.i₀ 1
def Y₀ : ℝ := D.c k (fr.depth 0) fr.i₀ 2 + fr.t₀ * D.c k (fr.depth 0) fr.i₀ 3 +
  D.c k (fr.depth 0) fr.i₀ 4 * fr.Z₀
/-- Parent hidden width. -/
def a₀ : ℝ := D.N k ^ (-fr.depth 0)

/-- An original affine function in the parent's contact chart. -/
def chartL (L : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![L 0 + L 1 * fr.t₀ + L 2 * fr.Z₀ + L 3 * fr.Y₀, fr.q₀ * (L 1 - fr.Z₀ * L 3),
    fr.q₀ * (L 2 + fr.t₀ * L 3), fr.q₀ ^ 2 * L 3]

/-- The parent's entry in chart coordinates. -/
def L₀ : Fin 4 → ℝ := fr.chartL (fr.pal 0 fr.i₀ fr.u₀)

/-- Residual trajectory coefficients: contact chart, then the parent residual. -/
def coeff (l : α) : Fin 6 → ℝ :=
  residualCoeff fr.L₀ fr.a₀ (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l))

/-- The residual affine part of a label's entry, in chart coordinates. -/
def resL (L : Fin 4 → ℝ) : Fin 4 → ℝ := fun e => (fr.chartL L e - fr.L₀ e) / fr.a₀

/-! ### Residual labels -/

/-- Residual block exponent at level `h`. -/
def resT (h : ℕ) : ℕ := fr.Tl h - fr.T₀

/-- The residual label fields at level `h`. -/
def level (h : ℕ) : LabelLevel α where
  n := (fr.retained h).card
  T := fr.resT h
  j := fun i => ⟨(((D.j k (fr.depth h) (fr.node h i).1 : ℕ) -
      (D.j k (fr.depth 0) fr.i₀ : ℕ) * 2 ^ fr.resT h) % 2 ^ fr.resT h),
      Nat.mod_lt _ (pow_pos two_pos _)⟩
  A := fun i => fr.hist h (fr.node h i).1 (fr.node h i).2
  B := fun i => fr.hist h (fr.node h i).1 (fr.node h i).2
  c := fun i => contactChartLabel fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.c k (fr.depth h) (fr.node h i).1)
  F := fun i => X 3 - affineBase
    (fr.resL (fr.pal h (fr.node h i).1 (lastEntry h (fr.node h i).2)))

end Frame

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
