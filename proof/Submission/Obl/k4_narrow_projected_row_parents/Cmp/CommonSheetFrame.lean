/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonSheetFrame.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonPhysicalFrame
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.AffineDomainBounds

/-! A native affine frame composed with the literal common-domain inverse. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Metric
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

noncomputable section

theorem affineBase_common_comp (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    (q χ g m : ℝ) (c : Code) (x : Fin 3 → ℝ) :
    affineBase A b (physicalBase q χ g m c x) =
      affineBase (A * physicalMatrix q χ g m c)
        (A.mulVec (physicalOffset q χ m c) + b) x := by
  rw [physicalBase_eq_affine]
  simp only [affineBase, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem common_comp_det_ne_zero (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.det ≠ 0)
    {q χ g m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (c : Code) :
    (A * physicalMatrix q χ g m c).det ≠ 0 := by
  rw [Matrix.det_mul]
  exact mul_ne_zero hA (physicalMatrix_det_ne_zero hq hχ hm c)

/-- Exact coordinate composition identifies the center of the stable ball with
the actual native base of the original physical source point. -/
theorem common_sheet_ball_containment (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ)
    {q χ g m ρ : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (hρ : 0 < ρ)
    (c : Code) (source : Fin 3 → ℝ)
    (hnorm : ‖WithLp.toLp 2 (coords q χ g m c source)‖ ≤ (1 : ℝ) / 8)
    (hrow : ∀ i, (∑ j, |(A * physicalMatrix q χ g m c) i j|) ≤ ρ / 20) :
    ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (WithLp.toLp 2 (fun i =>
        ((A.mulVec (physicalOffset q χ m c) + b) i : ℂ) +
          ∑ j, ((A * physicalMatrix q χ g m c) i j : ℂ) * z j) : EuclideanSpace ℂ (Fin 3)) ∈
      ball (emb (WithLp.toLp 2 (affineBase A b source))) ρ := by
  let M := A * physicalMatrix q χ g m c
  let d := A.mulVec (physicalOffset q χ m c) + b
  let x₀ : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (coords q χ g m c source)
  have hcenterR : affineBase M d (coords q χ g m c source) = affineBase A b source := by
    rw [← affineBase_common_comp, physicalBase_coords hq.ne' hχ.ne' hm.ne']
  have hcenterC :
      (WithLp.toLp 2 (fun i => (d i : ℂ) + ∑ j, (M i j : ℂ) * emb x₀ j) : EuclideanSpace ℂ (Fin 3)) =
        emb (WithLp.toLp 2 (affineBase A b source)) := by
    rw [← hcenterR]
    ext i
    simp [x₀, emb, affineBase, Matrix.mulVec, dotProduct, add_comm]
  have h := affine_ball_containment d M hρ hrow x₀ hnorm
  rwa [hcenterC] at h

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
