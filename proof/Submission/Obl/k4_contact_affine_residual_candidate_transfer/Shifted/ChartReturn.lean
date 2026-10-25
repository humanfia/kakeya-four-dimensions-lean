/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/Shifted/ChartReturn.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.FrameCoordinates
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ShiftedReturn
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.Statement

/-!
# Returning residual polynomials through the parent chart

For a frame `f`, the substitution `chartSubst f` writes the residual
coordinates of a trajectory as affine functions of the original base
coordinates and of the shifted hidden coordinate `w - L₀(base)`, where `L₀` is
the parent's original affine entry. Evaluated at the shifted point of the
original data it gives exactly the residual point of the frame
(`eval_chartSubst`). Only its hidden component depends on the hidden variable,
with derivative `a₀⁻¹`, so `shiftedChartPullback (chartSubst f) a₀` (from
`ShiftedReturn`) returns residual fits to shifted fits at width `a₀` times
the residual width, keeping the first hidden derivative.
-/

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_affine_residual_candidate_transfer
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}

/-- The residual coordinates as affine functions of the shifted original ones. -/
def chartSubst (f : Frame D k s₀ U') : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C f.q₀⁻¹ * (X 0 - C f.t₀), C f.q₀⁻¹ * (X 1 - C f.Z₀),
    C (f.q₀ ^ 2)⁻¹ * (X 2 - C f.Y₀ + C f.Z₀ * X 0 - C f.t₀ * X 1), C f.a₀⁻¹ * X 3]

/-- The parent's original affine entry. -/
def parentL (f : Frame D k s₀ U') : Fin 4 → ℝ := f.pal 0 f.i₀ f.u₀

theorem eval_chartSubst (f : Frame D k s₀ U') (l : α) (t : ℝ) :
    (fun i => eval (shiftedPoint D k (parentL f) l t) (chartSubst f i)) =
      point (f.coeff l) ((t - f.t₀) / f.q₀) := by
  have hbase := f.point_coeff_base l t
  have hhid := f.point_coeff_hidden l t
  have h0 : point (f.coeff l) ((t - f.t₀) / f.q₀) 0 = (t - f.t₀) / f.q₀ := by
    simp [point]
  have h1 : point (f.coeff l) ((t - f.t₀) / f.q₀) 1 = (D.x k l t 1 - f.Z₀) / f.q₀ := by
    have := congrFun hbase 1
    simpa [Function.comp, contactBaseFrame] using this
  have h2 : point (f.coeff l) ((t - f.t₀) / f.q₀) 2 =
      (D.x k l t 2 - f.Y₀ + f.Z₀ * t - f.t₀ * D.x k l t 1) / f.q₀ ^ 2 := by
    have := congrFun hbase 2
    simpa [Function.comp, contactBaseFrame, Data.x] using this
  have h3 : point (f.coeff l) ((t - f.t₀) / f.q₀) 3 =
      (D.x k l t 3 - (parentL f 0 + parentL f 1 * t + parentL f 2 * D.x k l t 1 +
        parentL f 3 * D.x k l t 2)) / f.a₀ := by
    rw [hhid]
    simp [Data.x, affineBase, parentL]
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
    rw [h0]
    simp [chartSubst, shiftedPoint]
    ring
  · simp only [Fin.mk_one, Fin.isValue] at h1 ⊢
    rw [h1]
    simp [chartSubst, shiftedPoint]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue] at h2 ⊢
    rw [h2]
    simp [chartSubst, shiftedPoint, Data.x]
    ring
  · simp only [Fin.reduceFinMk, Fin.isValue] at h3 ⊢
    rw [h3]
    simp [chartSubst, shiftedPoint]
    ring

theorem chartSubst_degree (f : Frame D k s₀ U') (i : Fin 4) :
    (chartSubst f i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_C_mul _ (deg1_sub (deg1_add (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _)))
  · exact deg1_C_mul _ (deg1_X _)

theorem pderiv_chartSubst (f : Frame D k s₀ U') (i : Fin 4) :
    pderiv (3 : Fin 4) (chartSubst f i) = if i = 3 then C f.a₀⁻¹ else 0 := by
  fin_cases i <;> simp [chartSubst, pderiv_X]

theorem coeffL1_chartSubst (f : Frame D k s₀ U') (i : Fin 4) :
    coeffL1 (chartSubst f i) ≤
      (|f.q₀⁻¹| + |(f.q₀ ^ 2)⁻¹| + |f.a₀⁻¹|) * (1 + |f.t₀| + |f.Z₀| + |f.Y₀|) := by
  have hA : 0 ≤ |f.q₀⁻¹| := abs_nonneg _
  have hB : 0 ≤ |(f.q₀ ^ 2)⁻¹| := abs_nonneg _
  have hC : 0 ≤ |f.a₀⁻¹| := abs_nonneg _
  have ht : 0 ≤ |f.t₀| := abs_nonneg _
  have hZ : 0 ≤ |f.Z₀| := abs_nonneg _
  have hY : 0 ≤ |f.Y₀| := abs_nonneg _
  have hsub (c : ℝ) (j : Fin 4) : coeffL1 (X j - C c : MvPolynomial (Fin 4) ℝ) ≤ 1 + |c| := by
    calc
      _ ≤ coeffL1 (X j : MvPolynomial (Fin 4) ℝ) + coeffL1 (C c : MvPolynomial (Fin 4) ℝ) :=
        coeffL1_sub_le _ _
      _ = 1 + |c| := by rw [coeffL1_X, coeffL1_C]
  have hCX (c : ℝ) (j : Fin 4) : coeffL1 (C c * X j : MvPolynomial (Fin 4) ℝ) ≤ |c| := by
    calc
      _ ≤ |c| * coeffL1 (X j : MvPolynomial (Fin 4) ℝ) := coeffL1_C_mul_le _ _
      _ = |c| := by rw [coeffL1_X, mul_one]
  fin_cases i
  · calc
      coeffL1 (chartSubst f 0) ≤ |f.q₀⁻¹| * (1 + |f.t₀|) :=
        (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hsub _ _) hA)
      _ ≤ _ := by nlinarith
  · calc
      coeffL1 (chartSubst f 1) ≤ |f.q₀⁻¹| * (1 + |f.Z₀|) :=
        (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hsub _ _) hA)
      _ ≤ _ := by nlinarith
  · have hin : coeffL1 (X 2 - C f.Y₀ + C f.Z₀ * X 0 - C f.t₀ * X 1 : MvPolynomial (Fin 4) ℝ) ≤
        1 + |f.Y₀| + |f.Z₀| + |f.t₀| := by
      calc
        _ ≤ coeffL1 (X 2 - C f.Y₀ + C f.Z₀ * X 0 : MvPolynomial (Fin 4) ℝ) +
            coeffL1 (C f.t₀ * X 1 : MvPolynomial (Fin 4) ℝ) := coeffL1_sub_le _ _
        _ ≤ (coeffL1 (X 2 - C f.Y₀ : MvPolynomial (Fin 4) ℝ) +
            coeffL1 (C f.Z₀ * X 0 : MvPolynomial (Fin 4) ℝ)) +
            coeffL1 (C f.t₀ * X 1 : MvPolynomial (Fin 4) ℝ) :=
          add_le_add (coeffL1_add_le _ _) le_rfl
        _ ≤ (1 + |f.Y₀| + |f.Z₀|) + |f.t₀| :=
          add_le_add (add_le_add (hsub _ _) (hCX _ _)) (hCX _ _)
        _ = _ := by ring
    calc
      coeffL1 (chartSubst f 2) ≤ |(f.q₀ ^ 2)⁻¹| * (1 + |f.Y₀| + |f.Z₀| + |f.t₀|) :=
        (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left hin hB)
      _ ≤ _ := by nlinarith
  · calc
      coeffL1 (chartSubst f 3) ≤ |f.a₀⁻¹| := hCX _ _
      _ ≤ _ := by nlinarith

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted
