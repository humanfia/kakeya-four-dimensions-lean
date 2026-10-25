import Submission.Obl.k4_physical_parent_potential_candidates.ConicTensor
import Submission.Obl.k4_physical_parent_potential_candidates.FubiniCurvature

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set
open scoped BigOperators

noncomputable section

namespace ConicTensor

/-- The cleared projection is linear in a scalar multiple of its tensor. -/
theorem cleared_const_mul (H : Matrix (Fin 3) (Fin 3) ℝ) (T : Tensor) (r : ℝ) (i j k : Fin 3) :
    cleared H (fun a b c => r*T a b c) i j k = r*cleared H T i j k := by
  simp only [cleared, fubiniCubic, Fin.sum_univ_three]
  ring

theorem cleared_add (H : Matrix (Fin 3) (Fin 3) ℝ) (S T : Tensor) (i j k : Fin 3) :
    cleared H (fun a b c => S a b c+T a b c) i j k =
      cleared H S i j k+cleared H T i j k := by
  simp only [cleared, fubiniCubic, Fin.sum_univ_three]
  ring

/-- The cubic identity for a graph in a quadratic level set survives
clearing: the parent quadratic contributes no error to this projection. -/
theorem cleared_of_implicit_identity (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (S T : Tensor) (n : Fin 3 → ℝ) (r : ℝ)
    (himp : ∀ i j k, T i j k = r*S i j k+fubiniCubic H n i j k) (i j k : Fin 3) :
    cleared H T i j k = r*cleared H S i j k := by
  have he : T = fun a b c => r*S a b c+fubiniCubic H n a b c := by
    funext a b c
    exact himp a b c
  rw [he, cleared_add, cleared_const_mul, cleared_fubini H hH, add_zero]

end ConicTensor

namespace FubiniHessian

/-- The polynomial-in-jets numerator of the canonical cubic error. -/
def clearedCubicError (f : FubiniBase → ℝ) (x : FubiniBase) : ConicTensor.Tensor :=
  ConicTensor.cleared (hessian f x) (cubic f x)

theorem adjugate_eq_det_mul_inverse (H : Matrix (Fin 3) (Fin 3) ℝ) (hdet : H.det ≠ 0)
    (i j : Fin 3) : H.adjugate i j = H.det*H⁻¹ i j := by
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [← mul_assoc, mul_inv_cancel₀ hdet, one_mul]

/-- The cleared tensor is exactly five times the Hessian determinant
multiplied by the actual canonical cubic defect of the graph. -/
theorem clearedCubicError_eq
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (i j k : Fin 3) :
    clearedCubicError f x i j k = 5*(hessian f x).det*cubicError f x i j k := by
  have ha := adjugate_eq_det_mul_inverse (hessian f x) (hdet x hx)
  simp only [clearedCubicError, ConicTensor.cleared, cubicError, fubiniCubic,
    form_eq_canonical hU hf hdet hx, canonical, ha, Fin.sum_univ_three]
  ring

/-- The cleared potential tensor is the exact scalar multiple of the
canonical graph error dictated by implicit differentiation of a quadratic. -/
theorem cleared_potential_eq_error
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (T : ConicTensor.Tensor) (n : Fin 3 → ℝ) (r : ℝ)
    (himp : ∀ i j k, T i j k = r*cubic f x i j k+fubiniCubic (hessian f x) n i j k)
    (i j k : Fin 3) :
    ConicTensor.cleared (hessian f x) T i j k =
      5*r*(hessian f x).det*cubicError f x i j k := by
  rw [ConicTensor.cleared_of_implicit_identity (hessian f x) (hessian_symmetric hU hf hx)
    (cubic f x) T n r himp]
  change r*clearedCubicError f x i j k = _
  rw [clearedCubicError_eq hU hf hdet hx]
  ring

/-- Dividing the cleared potential error uses only regularity of the
normalized Hessian and the implicit hidden derivative. -/
theorem cubicError_bound_of_cleared_potential
    {f : FubiniBase → ℝ} {U : Set FubiniBase} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 6 f U) (hdet : ∀ x ∈ U, (hessian f x).det ≠ 0)
    {x : FubiniBase} (hx : x ∈ U) (T : ConicTensor.Tensor) (n : Fin 3 → ℝ)
    {r κ ν ε : ℝ} (hκ : 0 < κ) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hr : κ ≤ |r|) (hH : ν ≤ |(hessian f x).det|)
    (himp : ∀ i j k, T i j k = r*cubic f x i j k+fubiniCubic (hessian f x) n i j k)
    (herr : ∀ i j k, |ConicTensor.cleared (hessian f x) T i j k| ≤ ε) :
    ∀ i j k, |cubicError f x i j k| ≤ ε/(5*κ*ν) := by
  intro i j k
  have he := herr i j k
  rw [cleared_potential_eq_error hU hf hdet hx T n r himp, abs_mul, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 5)] at he
  apply (le_div_iff₀ (by positivity : 0 < 5*κ*ν)).mpr
  calc
    _ = (5*κ*ν)*|cubicError f x i j k| := by ring
    _ ≤ (5*|r| *|(hessian f x).det|) *|cubicError f x i j k| := by
      gcongr
    _ ≤ ε := he

end FubiniHessian

end

end Submission.Obl.k4_physical_parent_potential_candidates
