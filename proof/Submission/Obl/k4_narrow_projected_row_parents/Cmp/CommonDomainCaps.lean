/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonDomainCaps.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomains
import Submission.Lib.K4AffineMeshCaps.Transport

/-! The actual affine comparison frame and its original-palette finite-mesh ceilings. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The matrix of the physical-base to comparison-base map. -/
def coordMatrix (q χ g m : ℝ) (c : Code) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / (100 * q), 0, 0;
    -(c 1 : ℝ) / 100, 1 / (100 * χ), 0;
    -((c 3 : ℝ) * g) / (100 * m), 0, 1 / (100 * m)]

def coordOffset (q χ g m : ℝ) (c : Code) : Fin 3 → ℝ :=
  ![-timeCenter q c / (100 * q), -(c 2 : ℝ) / 100,
    (timeCenter q c * ((c 3 : ℝ) * g) - (c 4 : ℝ) * m) / (100 * m)]

theorem coords_eq_affine {q χ g m : ℝ} (hq : q ≠ 0) (hχ : χ ≠ 0) (hm : m ≠ 0)
    (c : Code) (z : Fin 3 → ℝ) :
    coords q χ g m c z = Submission.Lib.K4AffineMeshCaps.affineBase
      (coordMatrix q χ g m c) (coordOffset q χ g m c) z := by
  ext i
  fin_cases i <;>
    simp [coords, coordMatrix, coordOffset, majorCenter, minorCenter,
      Submission.Lib.K4AffineMeshCaps.affineBase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> field_simp <;> ring

theorem coordMatrix_det (q χ g m : ℝ) (c : Code) :
    (coordMatrix q χ g m c).det = (100 * q)⁻¹ * (100 * χ)⁻¹ * (100 * m)⁻¹ := by
  simp [coordMatrix, Matrix.det_fin_three]

theorem coordMatrix_det_ne_zero {q χ g m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m)
    (c : Code) : (coordMatrix q χ g m c).det ≠ 0 := by
  rw [coordMatrix_det]
  positivity

/-- The inverse determinant is exactly the physical comparison volume. -/
theorem coordMatrix_inv_abs_det {q χ g m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m)
    (c : Code) : |(coordMatrix q χ g m c).det|⁻¹ = 1000000 * q * χ * m := by
  rw [coordMatrix_det, abs_of_pos (by positivity)]
  simp only [mul_inv_rev, inv_inv]
  ring

/-- Literal primitive base caps transfer to the common comparison frame with its
Jacobian, keeping the same source law, extra incidence event and original palette. -/
theorem common_frame_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {q χ g m δ σ C : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m)
    (c : Code) (hδ : 0 < δ) (hσ : 0 < σ) (hC : 0 ≤ C)
    (palette : ℝ≥0∞) (hp : palette ≠ ⊤)
    (hresolve : ∀ i, (∑ j, |coordMatrix q χ g m c i j| * δ) ≤ σ)
    (hcap : ∀ z : Fin 3 → ℤ,
      μ {p | Submission.Lib.K4MovingMeshBoxes.baseMesh δ (Z p) = z ∧ condition p} ≤
        ENNReal.ofReal (C * δ ^ 3) * palette) (z : Fin 3 → ℤ) :
    μ {p | Submission.Lib.K4MovingMeshBoxes.baseMesh σ (coords q χ g m c (Z p)) = z ∧ condition p} ≤
      ENNReal.ofReal (27000000 * C * q * χ * m * σ ^ 3) * palette := by
  have hscaled (z' : Fin 3 → ℤ) :
      μ {p | Submission.Lib.K4MovingMeshBoxes.baseMesh δ (Z p) = z' ∧ condition p} ≤
        ENNReal.ofReal ((C * palette.toReal) * δ ^ 3) := by
    convert hcap z' using 1
    rw [show (C * palette.toReal) * δ ^ 3 = (C * δ ^ 3) * palette.toReal by ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hp]
  have h := Submission.Lib.K4AffineMeshCaps.affine_mesh_cell_cap μ Z condition
    (coordMatrix q χ g m c) (coordOffset q χ g m c)
    (coordMatrix_det_ne_zero hq hχ hm c) hδ hσ (mul_nonneg hC ENNReal.toReal_nonneg)
    hresolve hscaled z
  simp_rw [← coords_eq_affine hq.ne' hχ.ne' hm.ne' c] at h
  rw [coordMatrix_inv_abs_det hq hχ hm c] at h
  have heq : 27 * (C * palette.toReal) * (1000000 * q * χ * m) * σ ^ 3 =
      (27000000 * C * q * χ * m * σ ^ 3) * palette.toReal := by ring
  rw [heq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hp] at h
  exact h

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
