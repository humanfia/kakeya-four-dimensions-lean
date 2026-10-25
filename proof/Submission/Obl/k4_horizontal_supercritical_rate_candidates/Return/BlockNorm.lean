import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Cells
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.ScalarBlock

/-!
# Block normalization of a candidate label

For a depth-`sc` label `iq`, its block starts at `tQ`, its first position is centred at `ZQ`,
and its coarse affine fit is that of its depth-`s₀` ancestor. Normalized coefficients give the
scalar coordinate `y = (x1 - ZQ)/q` and the value `x = (x3 - L_anc)/a₀`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace CoreData

variable {α : Type} [MeasurableSpace α] (D : CoreData α)

def tQ (iq : Fin D.fc.n) : ℝ := ((D.fc.j iq : ℕ) : ℝ) / 2 ^ D.fc.T
def ZQ (iq : Fin D.fc.n) : ℝ := D.fc.c iq 0 + D.tQ iq * D.fc.c iq 1

/-- The coarse fit of the ancestor (zero if none). -/
def Lanc (iq : Fin D.fc.n) : Fin 4 → ℝ := by
  classical
  exact if h : ∃ h₀ : Fin D.f₀.n, D.fc.A iq ⊆ D.f₀.A h₀ ∧ D.fc.I iq ⊆ D.f₀.I h₀
    then D.f₀.L (Classical.choose h) else 0

def ny0 (iq : Fin D.fc.n) (l : α) : ℝ := (D.b l 0 + D.tQ iq * D.b l 3 - D.ZQ iq) / D.fc.q
def ny1 (_iq : Fin D.fc.n) (l : α) : ℝ := D.b l 3
def ne0 (iq : Fin D.fc.n) (l : α) : ℝ :=
  D.b l 2 - D.Lanc iq 0 - D.Lanc iq 2 * D.b l 0 - D.Lanc iq 3 * D.b l 1
def ne1 (iq : Fin D.fc.n) (l : α) : ℝ :=
  D.b l 5 - D.Lanc iq 1 - D.Lanc iq 2 * D.b l 3 - D.Lanc iq 3 * D.b l 4
def nx0 (iq : Fin D.fc.n) (l : α) : ℝ := (D.ne0 iq l + D.tQ iq * D.ne1 iq l) / D.a₀
def nx1 (iq : Fin D.fc.n) (l : α) : ℝ := D.fc.q * D.ne1 iq l / D.a₀

/-- The block's value at a point is the normalized residual from the coarse fit. -/
theorem blockVal_eq (iq : Fin D.fc.n) (p : α × ℝ) (hq : D.fc.q ≠ 0) :
    blockVal (D.tQ iq) D.fc.q (D.nx0 iq) (D.nx1 iq) p =
      (x3 D.b p.1 p.2 - (D.Lanc iq 0 + D.Lanc iq 1 * p.2 + D.Lanc iq 2 * x1 D.b p.1 p.2 +
        D.Lanc iq 3 * x2 D.b p.1 p.2)) / D.a₀ := by
  unfold blockVal tau nx0 nx1 ne0 ne1 x1 x2 x3
  field_simp
  ring

/-- The block's scalar coordinate is the normalized first position. -/
theorem blockY_eq (iq : Fin D.fc.n) (p : α × ℝ) (hq : D.fc.q ≠ 0) :
    D.ny0 iq p.1 + tau (D.tQ iq) D.fc.q p.2 * D.ny1 iq p.1 =
      (x1 D.b p.1 p.2 - D.ZQ iq) / D.fc.q := by
  unfold ny0 ny1 tau x1
  field_simp
  ring

theorem measurable_ny0 {iq : Fin D.fc.n} (hb : Measurable D.b) : Measurable (D.ny0 iq) := by
  unfold ny0
  exact ((((measurable_pi_apply 0).comp hb).add
    (measurable_const.mul ((measurable_pi_apply 3).comp hb))).sub_const _).div_const _

theorem measurable_ny1 {iq : Fin D.fc.n} (hb : Measurable D.b) : Measurable (D.ny1 iq) := by
  unfold ny1; exact (measurable_pi_apply 3).comp hb

theorem measurable_nx0 {iq : Fin D.fc.n} (hb : Measurable D.b) : Measurable (D.nx0 iq) := by
  unfold nx0 ne0 ne1
  have h : ∀ k : Fin 6, Measurable (fun l => D.b l k) := fun k => (measurable_pi_apply k).comp hb
  refine Measurable.div_const ?_ _
  refine Measurable.add ?_ (measurable_const.mul ?_)
  · exact (((h 2).sub_const _).sub (measurable_const.mul (h 0))).sub (measurable_const.mul (h 1))
  · exact (((h 5).sub_const _).sub (measurable_const.mul (h 3))).sub (measurable_const.mul (h 4))

theorem measurable_nx1 {iq : Fin D.fc.n} (hb : Measurable D.b) : Measurable (D.nx1 iq) := by
  unfold nx1 ne1
  have h : ∀ k : Fin 6, Measurable (fun l => D.b l k) := fun k => (measurable_pi_apply k).comp hb
  refine Measurable.div_const (measurable_const.mul ?_) _
  exact (((h 5).sub_const _).sub (measurable_const.mul (h 3))).sub (measurable_const.mul (h 4))

end CoreData

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
