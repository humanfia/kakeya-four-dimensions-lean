/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowParent.lean.
   Its original row-parent code came from this LOT tree o222, session x0776,
   commit 6141c0189519ee10a8a74b6f7f39756f61c1639b,
   Submission/Obl/k4_projected_parent_contact_reduction/RowParent.lean. -/
import Submission.Obl.k4_narrow_projected_row_parents.Model
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.Zoom

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open Submission.Obl.k4_general_parent_projected_layers Submission.Obl.k4_general_parent_projected_layers.PreparedModel
open Submission.Obl.k4_general_parent_projected_layers.NativeMesh

noncomputable section

namespace PreparedModel


variable {α : Type} [MeasurableSpace α]

/-- Left end of a dyadic block. -/
def blockStart (T : ℕ) (j : Fin (2 ^ T)) : ℝ := (j : ℝ) / (2 : ℝ) ^ T

theorem blockStart_mem (T : ℕ) (j : Fin (2 ^ T)) : blockStart T j ∈ interval T j := by
  constructor
  · exact le_rfl
  · unfold blockStart
    gcongr
    linarith

theorem q_pos (a : PreparedModel α) (k : ℕ) (s : ℝ) : 0 < a.q k s := by
  unfold q; positivity

theorem interval_eq (T : ℕ) (j : Fin (2 ^ T)) :
    interval T j = Icc (blockStart T j) (blockStart T j + (2 : ℝ) ^ (-(T : ℤ))) := by
  unfold interval blockStart
  congr 1
  rw [zpow_neg, zpow_natCast, add_div, div_eq_mul_inv (1 : ℝ), one_mul]

/-- The zoom of a parent label: block start and length, major centre at the
block start, the tilted transverse box, and hidden width `a_r`. -/
def parentZoom (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) : Zoom where
  t₀ := blockStart (a.T k r) (a.j k r Q)
  q := a.q k r
  z₀ := a.c k r Q 0 + blockStart (a.T k r) (a.j k r Q) * a.c k r Q 1
  c₂ := a.c k r Q 2
  c₃ := a.c k r Q 3
  c₄ := a.c k r Q 4
  w := a.q k r * narrow p k r
  h₀ := 0
  a := width p k r

theorem narrow_pos (p : Parameters) (hp : p.Valid) (k : ℕ) (s : ℝ) : 0 < narrow p k s := by
  unfold narrow
  exact Real.rpow_pos_of_pos (by linarith [hp.1 k]) _

theorem width_pos (p : Parameters) (hp : p.Valid) (k : ℕ) (s : ℝ) : 0 < width p k s := by
  unfold width
  exact Real.rpow_pos_of_pos (by linarith [hp.1 k]) _

theorem parentZoom_ok (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) : (parentZoom p a k r Q).Ok where
  q_ne := (q_pos a k r).ne'
  w_ne := (mul_pos (q_pos a k r) (narrow_pos p hp k r)).ne'
  a_ne := (width_pos p hp k r).ne'

end PreparedModel

open PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- A zoomed parent with a dense set of incidences obeying a fitted row. -/
structure RowParent (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (E M : ℝ) where
  /-- the parent label -/
  Q : Fin (a.n k r)
  /-- the constant row -/
  B : Fin 2 → ℝ
  /-- the skew coefficient -/
  lam : ℝ
  /-- incidences where the row equation holds -/
  G : Set (α × ℝ)
  measurable_G : MeasurableSet G
  G_sub : G ⊆ a.B k r Q ×ˢ a.block k r Q
  mass : ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r Q) ≤ a.rho k G
  B_le : |B 0| + |B 1| ≤ M
  lam_le : |lam| ≤ M
  row : ∀ z ∈ G,
    |(parentZoom p a k r Q).coeff (a.b k z.1) 4 - B 0 - B 1 * a.b k z.1 3 +
      lam * (parentZoom p a k r Q).coeff (a.b k z.1) 0| ≤ E

end

end Submission.Obl.k4_narrow_projected_row_parents
