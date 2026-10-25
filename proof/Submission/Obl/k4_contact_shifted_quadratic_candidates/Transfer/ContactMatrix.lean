/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/ContactMatrix.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open Matrix

noncomputable section

def contactBaseFrame (t₀ q Z₀ Y₀ : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(z 0 - t₀) / q, (z 1 - Z₀) / q, (z 2 - Y₀ + Z₀ * z 0 - t₀ * z 1) / q ^ 2]

def contactFrameMatrix (t₀ q Z₀ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q⁻¹, 0, 0; 0, q⁻¹, 0; Z₀ / q ^ 2, -t₀ / q ^ 2, (q ^ 2)⁻¹]

def contactFrameOffset (t₀ q Z₀ Y₀ : ℝ) : Fin 3 → ℝ :=
  ![-t₀ / q, -Z₀ / q, -Y₀ / q ^ 2]

theorem contactBaseFrame_eq_affine (t₀ q Z₀ Y₀ : ℝ) (z : Fin 3 → ℝ) :
    contactBaseFrame t₀ q Z₀ Y₀ z =
      (contactFrameMatrix t₀ q Z₀).mulVec z + contactFrameOffset t₀ q Z₀ Y₀ := by
  funext i
  fin_cases i <;>
    simp [contactBaseFrame, contactFrameMatrix, contactFrameOffset,
      dotProduct, Fin.sum_univ_three, div_eq_mul_inv] <;> ring

/-- The base contact chart has exactly the fourth-power Jacobian. -/
theorem det_contactFrameMatrix (t₀ q Z₀ : ℝ) :
    (contactFrameMatrix t₀ q Z₀).det = (q ^ 4)⁻¹ := by
  simp [contactFrameMatrix, Matrix.det_fin_three, ← inv_pow] <;> ring

theorem det_contactFrameMatrix_ne_zero (t₀ Z₀ : ℝ) {q : ℝ} (hq : q ≠ 0) :
    (contactFrameMatrix t₀ q Z₀).det ≠ 0 := by
  rw [det_contactFrameMatrix]
  exact inv_ne_zero (pow_ne_zero _ hq)

end
end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
