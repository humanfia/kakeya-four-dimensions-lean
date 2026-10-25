import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ResidualData
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Dyadic

/-!
# Exact algebra of the residual coordinates

The residual coordinates of a trajectory are its parent contact chart followed
by the parent residual. The base coordinates and the velocity rows only see the
chart; the hidden coordinate is `(w - L₀) / a₀`. A label's residual test
`X 3 - affineBase (resL L)` evaluates to `(w - L) / a₀` in original terms, with
hidden derivative one.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization

noncomputable section

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (fr : Frame D k s₀ U')

theorem coeff_base (l : α) (i : Fin 6) (hi : i ≠ 2 ∧ i ≠ 5) :
    fr.coeff l i = contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l) i := by
  fin_cases i <;> simp_all [coeff, residualCoeff]

theorem point_coeff_one (l : α) (τ : ℝ) :
    point (fr.coeff l) τ 1 = point (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l)) τ 1 := by
  simp [point, coeff, residualCoeff]

theorem point_coeff_two (l : α) (τ : ℝ) :
    point (fr.coeff l) τ 2 = point (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l)) τ 2 := by
  simp [point, coeff, residualCoeff]

/-- The parent block length is positive. -/
theorem q₀_pos : 0 < fr.q₀ := by unfold q₀; positivity

/-- An original affine function, read in the parent chart. -/
theorem eval_chartL (L : Fin 4 → ℝ) (b : Fin 6 → ℝ) (τ : ℝ) :
    eval (point (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ b) τ) (affineBase (fr.chartL L)) =
      eval (point b (fr.t₀ + fr.q₀ * τ)) (affineBase L) := by
  have hq := fr.q₀_pos.ne'
  simp [affineBase, chartL, point, contactChartCoeff]
  field_simp
  ring

/-- The hidden coordinate of the residual chart. -/
theorem point_coeff_three (l : α) (τ : ℝ) :
    point (fr.coeff l) τ 3 =
      (point (D.b k l) (fr.t₀ + fr.q₀ * τ) 3 -
        eval (point (D.b k l) (fr.t₀ + fr.q₀ * τ)) (affineBase (fr.pal 0 fr.i₀ fr.u₀))) /
        fr.a₀ := by
  have h := eval_residualSubst fr.L₀ fr.a₀
    (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l)) τ
  have h3 := congrFun h 3
  simp only [residualSubst, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons,
    Matrix.cons_val_succ, eval_mul, eval_C, eval_sub, eval_X] at h3
  have hchart := fr.eval_chartL (fr.pal 0 fr.i₀ fr.u₀) (D.b k l) τ
  have hw : point (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l)) τ 3 =
      point (D.b k l) (fr.t₀ + fr.q₀ * τ) 3 := by
    simp [point, contactChartCoeff]; ring
  rw [coeff, ← h3, L₀, hchart, hw]
  ring

/-- A label's residual test evaluates to its original fit divided by `a₀`. -/
theorem a₀_pos (hN : 0 < D.N k) : 0 < fr.a₀ := by unfold a₀; positivity

theorem eval_resTest (hN : 0 < D.N k) (l : α) (L : Fin 4 → ℝ) (τ : ℝ) :
    eval (point (fr.coeff l) τ) (X 3 - affineBase (fr.resL L)) =
      (point (D.b k l) (fr.t₀ + fr.q₀ * τ) 3 -
        eval (point (D.b k l) (fr.t₀ + fr.q₀ * τ)) (affineBase L)) / fr.a₀ := by
  have ha := (fr.a₀_pos hN).ne'
  have hthree := fr.point_coeff_three l τ
  have hchart := fr.eval_chartL L (D.b k l) τ
  have hchart₀ := fr.eval_chartL (fr.pal 0 fr.i₀ fr.u₀) (D.b k l) τ
  have h1 := fr.point_coeff_one l τ
  have h2 := fr.point_coeff_two l τ
  have hP : point (fr.coeff l) τ 0 =
      point (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l)) τ 0 := by
    simp [point]
  simp only [affineBase, eval_sub, eval_X, eval_add, eval_mul, eval_C] at hchart hchart₀ hthree ⊢
  rw [hthree, hP, h1, h2]
  simp only [resL, L₀]
  field_simp
  linear_combination (-1 : ℝ) * hchart + hchart₀

theorem pderiv_resTest (L : Fin 4 → ℝ) :
    pderiv (3 : Fin 4) (X 3 - affineBase L) = 1 := by
  simp [affineBase, pderiv_X]

theorem resTest_degree (L : Fin 4 → ℝ) : (X 3 - affineBase L).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le ((totalDegree_X _).le.trans (by norm_num))
    ((affineBase_degree L).trans (by norm_num)))

end Frame

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
