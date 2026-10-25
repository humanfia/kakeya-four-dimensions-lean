-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/CommonPhysicalFrame.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonPhysicalFrame.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomainCaps

/-! The explicit inverse frame used to compose native and projected sheets. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain

noncomputable section

def physicalBase (q χ g m : ℝ) (c : Code) (x : (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  let t := timeCenter q c + 100 * q * x 0
  ![t, majorCenter χ c t + 100 * χ * x 1,
    minorCenter q g m c t + 100 * m * x 2]

def physicalMatrix (q χ g m : ℝ) (c : Code) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![100 * q, 0, 0;
    100 * q * (c 1 : ℝ) * χ, 100 * χ, 0;
    100 * q * (c 3 : ℝ) * g, 0, 100 * m]

def physicalOffset (q χ m : ℝ) (c : Code) : Fin 3 → ℝ :=
  ![timeCenter q c, majorCenter χ c (timeCenter q c), (c 4 : ℝ) * m]

theorem physicalBase_eq_affine (q χ g m : ℝ) (c : Code) (x : (Fin 3 → ℝ)) :
    physicalBase q χ g m c x = Submission.Lib.K4AffineMeshCaps.affineBase
      (physicalMatrix q χ g m c) (physicalOffset q χ m c) x := by
  ext i
  fin_cases i <;>
    simp [physicalBase, physicalMatrix, physicalOffset, majorCenter, minorCenter,
      Submission.Lib.K4AffineMeshCaps.affineBase, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;> ring

theorem physicalMatrix_det (q χ g m : ℝ) (c : Code) :
    (physicalMatrix q χ g m c).det = 1000000 * q * χ * m := by
  simp [physicalMatrix, Matrix.det_fin_three]
  ring

theorem physicalMatrix_det_ne_zero {q χ g m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m)
    (c : Code) : (physicalMatrix q χ g m c).det ≠ 0 := by
  rw [physicalMatrix_det]
  positivity

theorem physicalBase_coords {q χ g m : ℝ} (hq : q ≠ 0) (hχ : χ ≠ 0) (hm : m ≠ 0)
    (c : Code) (z : Fin 3 → ℝ) : physicalBase q χ g m c (coords q χ g m c z) = z := by
  ext i
  fin_cases i <;> simp [physicalBase, coords, majorCenter, minorCenter] <;> field_simp <;> ring

theorem coords_physicalBase {q χ g m : ℝ} (hq : q ≠ 0) (hχ : χ ≠ 0) (hm : m ≠ 0)
    (c : Code) (x : (Fin 3 → ℝ)) : coords q χ g m c (physicalBase q χ g m c x) = x := by
  ext i
  fin_cases i <;> simp [physicalBase, coords, majorCenter, minorCenter] <;> field_simp <;> ring

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.CommonDomain
