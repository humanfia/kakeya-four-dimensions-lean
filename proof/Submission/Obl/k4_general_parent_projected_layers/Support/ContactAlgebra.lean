/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ContactAlgebra.lean. -/
import Submission.Lib.K4ContactNormalization.RowNormalization
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-!
The affine coordinate change after the row fit. The row error becomes a
constant along each trajectory, giving either a velocity strip or contact.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set

noncomputable section

/-- The frozen trajectory coordinates. -/
abbrev trajectory := Submission.Lib.K4ContactNormalization.point

/-- Subtract the fitted constant row and divide by its skew coefficient. -/
abbrev contactCoefficients := Submission.Lib.K4ContactNormalization.skewCoeff

/-- The corresponding affine change of position coordinates. -/
def contactPosition (B : Fin 2 → ℝ) (lam : ℝ) (z : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![z 0, z 1, (z 2 - B 0 * z 0 - B 1 * z 1) / lam, z 3]

theorem trajectory_contactCoefficients (B : Fin 2 → ℝ) (lam : ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    trajectory (contactCoefficients B lam b) t = contactPosition B lam (trajectory b t) := by
  ext i
  fin_cases i <;> simp [trajectory, contactCoefficients, contactPosition,
    Submission.Lib.K4ContactNormalization.point, Submission.Lib.K4ContactNormalization.skewCoeff] <;> ring

theorem measurable_contactCoefficients (B : Fin 2 → ℝ) (lam : ℝ) :
    Measurable (contactCoefficients B lam) := by
  unfold contactCoefficients Submission.Lib.K4ContactNormalization.skewCoeff
  fun_prop

/-- The skew row has constant evaluation along each affine trajectory. -/
theorem row_contact_identity (b : Fin 6 → ℝ) (t : ℝ) (T B : Fin 2 → ℝ)
    (lam : ℝ) :
    b 4 - B 0 - B 1 * b 3 + lam * b 0 =
      (b 4 - (T 0 + b 3 * T 1)) +
        (T 0 - B 0 + lam * (b 0 + t * b 3)) +
        b 3 * (T 1 - B 1 - lam * t) := by
  simpa only [mul_comm (b 3) (B 1)] using
    Submission.Lib.K4ContactNormalization.skew_row_identity B T lam (b 0) (b 3) (b 4) t

theorem row_contact_error {b : Fin 6 → ℝ} {t : ℝ} {T B : Fin 2 → ℝ}
    {lam delta rowError : ℝ}
    (hrow : |T 0 + b 3 * T 1 - b 4| ≤ rowError)
    (hzero : |T 0 - B 0 + lam * (b 0 + t * b 3)| ≤ delta)
    (hone : |T 1 - B 1 - lam * t| ≤ delta) :
    |b 4 - B 0 - B 1 * b 3 + lam * b 0| ≤
      rowError + (1 + |b 3|) * delta := by
  have hrow' : |b 4 - (T 0 + b 3 * T 1)| ≤ rowError := by
    simpa only [abs_sub_comm] using hrow
  simpa only [mul_comm (b 3) (B 1)] using
    Submission.Lib.K4ContactNormalization.row_fit_equation hrow' hzero hone

theorem contactCoefficients_error {b : Fin 6 → ℝ} {B : Fin 2 → ℝ}
    {lam error : ℝ} (hlam : lam ≠ 0)
    (h : |b 4 - B 0 - B 1 * b 3 + lam * b 0| ≤ error) :
    |contactCoefficients B lam b 4 + contactCoefficients B lam b 0| ≤ error / |lam| := by
  rw [Submission.Lib.K4ContactNormalization.horizontal_error B hlam b]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  simpa only [mul_comm (b 3) (B 1)] using h

theorem velocity_strip_error {b : Fin 6 → ℝ} {B : Fin 2 → ℝ}
    {lam error : ℝ}
    (h : |b 4 - B 0 - B 1 * b 3 + lam * b 0| ≤ error) :
    |b 4 - B 0 - B 1 * b 3| ≤ error + |lam| * |b 0| := by
  have h' : |b 4 - B 0 - b 3 * B 1 + lam * b 0| ≤ error := by
    simpa only [mul_comm (b 3) (B 1)] using h
  simpa only [mul_comm (b 3) (B 1)] using
    Submission.Lib.K4ContactNormalization.strip_of_small_skew h' le_rfl le_rfl

end

end Submission.Obl.k4_general_parent_projected_layers
