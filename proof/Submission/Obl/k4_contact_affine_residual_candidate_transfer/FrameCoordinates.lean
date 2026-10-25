import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameAlgebra
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ContactAffine

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

theorem residual_point_base (L : Fin 4 → ℝ) (a : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    point (residualCoeff L a b) t ∘ Fin.castSucc = point b t ∘ Fin.castSucc := by
  funext i
  fin_cases i <;> rfl

theorem residual_point_hidden (L : Fin 4 → ℝ) (a : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    point (residualCoeff L a b) t 3 =
      (point b t 3 - eval (point b t) (affineBase L)) / a := by
  simp [point, residualCoeff, affineBase, div_eq_mul_inv]
  ring

namespace Frame

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable (fr : Frame D k s₀ U')

theorem depth_zero : fr.depth 0 = s₀ := by simp [depth, frameDepth]

theorem parent_block : fr.block 0 fr.i₀ = Icc fr.t₀ (fr.t₀ + fr.q₀) := by
  simp only [block, Data.I, t₀, left, q₀, T₀, div_eq_mul_inv, add_mul, one_mul]

theorem measurable_toChart : Measurable fr.toChart :=
  measurable_fst.prodMk ((measurable_snd.sub_const fr.t₀).div_const fr.q₀)

theorem measurable_coeff (hb : Measurable (D.b k)) : Measurable fr.coeff := by
  unfold coeff residualCoeff contactChartCoeff
  fun_prop

theorem coeff_velocity (l : α) : fr.coeff l 3 = D.b k l 3 := rfl

theorem coeff_contact (l : α) : fr.coeff l 4 + fr.coeff l 0 =
    (D.b k l 4 + D.b k l 0) / fr.q₀ :=
  contactChart_contact_error fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l)

theorem eval_chartL_coordinates (L : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    eval (contactChartPoint fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ x) (affineBase (fr.chartL L)) =
      eval x (affineBase L) := by
  simpa [affineBase, chartL, contactChartPoint, contactAffineCoeff] using
    contactAffine_value fr.t₀ fr.Z₀ fr.Y₀ fr.q₀_pos.ne' L (x 0) (x 1) (x 2)

theorem point_contact_at_time (l : α) (t : ℝ) :
    point (contactChartCoeff fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.b k l))
      ((t - fr.t₀) / fr.q₀) = contactChartPoint fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.x k l t) := by
  rw [point_contactChartCoeff _ _ _ _ fr.q₀_pos.ne']
  have ht : fr.t₀ + fr.q₀ * ((t - fr.t₀) / fr.q₀) = t := by
    field_simp [fr.q₀_pos.ne'] <;> ring
  rw [ht]
  rfl

/-- The residual base coordinates are the exact affine contact chart of the
original base. -/
theorem point_coeff_base (l : α) (t : ℝ) :
    point (fr.coeff l) ((t - fr.t₀) / fr.q₀) ∘ Fin.castSucc =
      contactBaseFrame fr.t₀ fr.q₀ fr.Z₀ fr.Y₀ (D.x k l t ∘ Fin.castSucc) := by
  rw [coeff, residual_point_base, fr.point_contact_at_time]
  funext i
  fin_cases i <;> rfl

/-- The residual hidden coordinate uses the original affine entry, even
when that entry has arbitrarily large coefficients. -/
theorem point_coeff_hidden (l : α) (t : ℝ) :
    point (fr.coeff l) ((t - fr.t₀) / fr.q₀) 3 =
      ((D.x k l t) 3 - eval (D.x k l t) (affineBase (fr.pal 0 fr.i₀ fr.u₀))) / fr.a₀ := by
  rw [coeff, residual_point_hidden, fr.point_contact_at_time, L₀, fr.eval_chartL_coordinates]
  rfl

end Frame

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
