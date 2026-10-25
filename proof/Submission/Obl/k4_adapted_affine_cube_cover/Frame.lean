import Submission.Lib.K4PolynomialGeometry.Frame
import Submission.Obl.k4_adapted_affine_cube_cover.Body

namespace Submission.Obl.k4_adapted_affine_cube_cover

open MeasureTheory Set Module
open Submission.Lib.K4PolynomialGeometry

/-- A maximal determinant frame has admissible directions and captures the unit body's volume. -/
theorem exists_adapted_basis {n : ℕ}
    (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hV : Continuous V)
    (hdom : ∀ x, ‖x‖ ≤ V x) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, V (b i) ≤ 1) ∧
      (∀ i, ‖b i‖ ≤ 1) ∧
      (volume {x : EuclideanSpace ℝ (Fin n) | V x ≤ 1}).toReal / (2 : ℝ) ^ n ≤
        |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b| := by
  obtain ⟨b₀, hb₀⟩ := exists_basis_in_unit_body V
  obtain ⟨b, hb, hcoord⟩ := exists_compact_bounded_basis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (isCompact_unit_body V hV hdom) b₀ hb₀
  refine ⟨b, hb, fun i => (hdom (b i)).trans (hb i), ?_⟩
  simpa only [frameEquiv_det] using det_frame_ge_volume_div b hcoord

end Submission.Obl.k4_adapted_affine_cube_cover
