-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ParentFrame
import Submission.Obl.k4_scalar_guarded_tangent_preparation.CodeVelocity

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4XInterface
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

namespace PFrame

/-- Read a native major-velocity center from an original planar code.
Only the major inverse row occurs, so the minor scale has no cost. -/
def majorVelocityCenter (Φ : PFrame) (fine : ℝ) (code : Fin 2 → ℤ) : ℝ :=
  Φ.F.q * (Φ.F.D⁻¹ 0 0 * ((code 0 : ℝ) * fine - Φ.F.u 0) +
    Φ.F.D⁻¹ 0 1 * ((code 1 : ℝ) * fine - Φ.F.u 1))

theorem majorVelocityCenter_close (Φ : PFrame) {fine H : ℝ} (hfine : 0 < fine)
    (hrow : |Φ.F.q| * (|Φ.F.D⁻¹ 0 0| + |Φ.F.D⁻¹ 0 1|) ≤ H)
    (l : ℕ × (Fin 6 → ℝ)) (code : Fin 2 → ℤ)
    (hcode : ∀ e, code e = ⌊gv l e / fine⌋) :
    |Φ.eb l 3 - Φ.majorVelocityCenter fine code| ≤ H * fine := by
  have h0 := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error
    hfine (code 0) (hcode 0).symm
  have h1 := Submission.Obl.k4_scalar_guarded_tangent_preparation.floor_center_error
    hfine (code 1) (hcode 1).symm
  have heq : Φ.eb l 3 - Φ.majorVelocityCenter fine code =
      (Φ.F.q * Φ.F.D⁻¹ 0 0) * (gv l 0 - (code 0 : ℝ) * fine) +
      (Φ.F.q * Φ.F.D⁻¹ 0 1) * (gv l 1 - (code 1 : ℝ) * fine) := by
    simp [eb, Frame.normCoeff, majorVelocityCenter, gv] <;> ring
  rw [heq]
  calc
    _ ≤ |(Φ.F.q * Φ.F.D⁻¹ 0 0) * (gv l 0 - (code 0 : ℝ) * fine)| +
        |(Φ.F.q * Φ.F.D⁻¹ 0 1) * (gv l 1 - (code 1 : ℝ) * fine)| := abs_add_le _ _
    _ = |Φ.F.q * Φ.F.D⁻¹ 0 0| * |gv l 0 - (code 0 : ℝ) * fine| +
        |Φ.F.q * Φ.F.D⁻¹ 0 1| * |gv l 1 - (code 1 : ℝ) * fine| := by
      rw [abs_mul (Φ.F.q * Φ.F.D⁻¹ 0 0), abs_mul (Φ.F.q * Φ.F.D⁻¹ 0 1)]
    _ ≤ |Φ.F.q * Φ.F.D⁻¹ 0 0| * fine + |Φ.F.q * Φ.F.D⁻¹ 0 1| * fine :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = (|Φ.F.q| * (|Φ.F.D⁻¹ 0 0| + |Φ.F.D⁻¹ 0 1|)) * fine := by
      simp only [abs_mul]
      ring
    _ ≤ H * fine := mul_le_mul_of_nonneg_right hrow hfine.le

end PFrame

end
end Submission.Obl.k4_finite_affine_parent_sources
