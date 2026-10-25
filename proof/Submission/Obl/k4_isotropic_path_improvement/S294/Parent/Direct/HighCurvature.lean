-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Direct.HighCurvature, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/Direct/HighCurvature.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct.AffineBackground
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.HighCurvature
import Submission.Obl.k4_paired_test_normalization.Rescaling

/-! The actual high-curvature old test supplies a single affine background
for the physical parent. No bound on the background's coefficients is
assumed or asserted here. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct

open MvPolynomial
open Submission.Lib.K4GlobalParentSignal
open Submission.Obl.k4_quadratic_atlas_normalization

noncomputable section

/-- High hidden curvature of the OLD test gives a common affine hidden
sheet at distance `κ^6*a/B`, with its true hidden derivative unit `B`. -/
theorem high_curvature_affine_sheet (R : Po) (hR : R.totalDegree ≤ 2)
    {κ a B : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hB : 0 < B)
    (hlarge : B^2/(κ^5*a) ≤ |curvature R 3|) :
    ∃ L : Fin 4 → ℝ, ∀ z : Fin 4 → ℝ,
      |eval z (pderiv (3 : Fin 4) R)| ≤ κ*B →
      |z 3-(L 0+L 1*z 0+L 2*z 1+L 3*z 2)| ≤ κ^6*a/B := by
  let Rn : Po := C B⁻¹*R
  have hRn : Rn.totalDegree ≤ 2 :=
    (Submission.Obl.k4_paired_test_normalization.totalDegree_C_mul_le R B⁻¹).trans hR
  have hcurv : |curvature Rn 3| = |curvature R 3|/B := by
    rw [Submission.Obl.k4_paired_test_normalization.curvature_C_mul,
      abs_mul, abs_of_pos (inv_pos.mpr hB)]
    ring
  have hlarge' : (κ^5*(a/B))⁻¹ ≤ |curvature Rn 3| := by
    rw [hcurv]
    have heq : (κ^5*(a/B))⁻¹ = (B^2/(κ^5*a))/B := by field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hlarge hB.le
  obtain ⟨L,hL⟩ :=
    Submission.Obl.k4_contact_fine_labels_from_coarse_cover.high_curvature_affine_entry
      Rn hRn hκ (div_pos ha hB) hlarge'
  refine ⟨L,fun z hz => ?_⟩
  have hn : |eval z (pderiv (3 : Fin 4) Rn)| ≤ κ := by
    change |eval z (pderiv (3 : Fin 4) (C B⁻¹*R))| ≤ _
    rw [pderiv_C_mul, eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹*(κ*B) := mul_le_mul_of_nonneg_left hz (inv_pos.mpr hB).le
      _ = κ := by field_simp
  simpa only [mul_div_assoc] using hL z hn

/-- On every original line close to this affine sheet, subtracting the
physical background leaves a quadratic signal of thickness size. -/
theorem physical_residual_of_high_curvature
    (R P : Po) (hR : R.totalDegree ≤ 2) (hP : P.totalDegree ≤ 2)
    {κ a B : ℝ} (hκ : 0 < κ) (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 < B)
    (hlarge : B^2/(κ^5*a) ≤ |curvature R 3|) :
    ∃ L : Fin 4 → ℝ,
      (affineResidual L P).totalDegree ≤ 2 ∧
      pderiv (3 : Fin 4) (affineResidual L P) = pderiv (3 : Fin 4) P ∧
      ∀ (z : Fin 4 → ℝ) (K : ℝ), 0 ≤ K →
        |eval z (pderiv (3 : Fin 4) R)| ≤ κ*B →
        |eval z (pderiv (3 : Fin 4) P)| ≤ K*B →
        |curvature P 3| ≤ K*B^2 →
        |eval z (affineResidual L P)| ≤ K*(κ^6+(κ^6)^2)*a := by
  obtain ⟨L,hL⟩ := high_curvature_affine_sheet R hR hκ ha hB hlarge
  refine ⟨L,(affineResidual_degree L P).trans hP,pderiv_affineResidual L P,?_⟩
  intro z K hK hz hfirst hsecond
  exact affineResidual_value_scale L P hP z hK hB ha.le ha1
    (pow_nonneg hκ.le _) hfirst hsecond (hL z hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct
