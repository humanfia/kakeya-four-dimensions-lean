-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ParentFrame
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.Atlas

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4XInterface
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

namespace PFrame

/-- Read the actual original velocity from the two native planar
velocities. The full original trajectory label is unchanged. -/
theorem original_velocity_coordinates (Φ : PFrame) (hq : Φ.F.q ≠ 0)
    (hD : IsUnit Φ.F.D.det) (l : ℕ × (Fin 6 → ℝ)) (e : Fin 2) :
    gv l e = Φ.F.u e + Φ.F.q⁻¹ *
      ∑ i : Fin 2, Φ.F.D e i * (![Φ.eb l 3, Φ.eb l 4] : Fin 2 → ℝ) i := by
  have h := Φ.F.denormCoeff_normCoeff hq hD l.2
  fin_cases e
  · simpa [Frame.denormCoeff, eb, gv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      using (congrFun h (3 : Fin 6)).symm
  · simpa [Frame.denormCoeff, eb, gv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      using (congrFun h (4 : Fin 6)).symm

/-- A physical column bound divides by exactly the parent time unit. -/
theorem normalized_velocity_entry_le (Φ : PFrame) (hq : 0 < Φ.F.q)
    (e i : Fin 2) (C : ℝ) (h : |Φ.F.D e i| ≤ C * Φ.F.q) :
    |(Φ.F.q⁻¹ • Φ.F.D) e i| ≤ C := by
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hq)]
  calc
    _ ≤ Φ.F.q⁻¹ * (C * Φ.F.q) := mul_le_mul_of_nonneg_left h (inv_pos.mpr hq).le
    _ = C := by field_simp [hq.ne']

end PFrame

end Submission.Obl.k4_finite_affine_parent_sources
