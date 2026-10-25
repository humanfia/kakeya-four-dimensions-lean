import Mathlib

/-!
Adapted from: here:o062
Original proof: x0212, commit cea4c82,
Submission/Obl/k4_scalar_mesh_projection/AffineCurl.lean.

Affine changes of scalar base coordinates, including the exact determinant
factor in the curl of a pulled-back polynomial row field.
-/

namespace Submission.Lib.K4PolynomialPotential

open MvPolynomial

noncomputable def scalarAffineHom (a : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.aeval (fun i => C (a i) + C (L i 0) * X 0 + C (L i 1) * X 1)

theorem eval_scalarAffineHom (P : MvPolynomial (Fin 2) ℝ)
    (a z : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ) :
    eval z (scalarAffineHom a L P) =
      eval (fun i => a i + L i 0 * z 0 + L i 1 * z 1) P := by
  have h := MvPolynomial.comp_aeval_apply
    (f := fun i => C (a i) + C (L i 0) * X 0 + C (L i 1) * X 1)
    (MvPolynomial.aeval z) P
  simpa only [scalarAffineHom, MvPolynomial.aeval_eq_eval, map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X] using h

theorem pderiv_scalarAffineHom (P : MvPolynomial (Fin 2) ℝ)
    (a : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ) (i : Fin 2) :
    pderiv i (scalarAffineHom a L P) =
      C (L 0 i) * scalarAffineHom a L (pderiv 0 P) +
        C (L 1 i) * scalarAffineHom a L (pderiv 1 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [scalarAffineHom]
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ]
    ring
  | mul_X P j hP =>
    simp only [map_mul, pderiv_mul, map_add, hP]
    fin_cases i <;> fin_cases j <;> simp [scalarAffineHom, pderiv_C_mul] <;> ring

noncomputable def scalarRowPullback (a : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ)
    (A B : MvPolynomial (Fin 2) ℝ) (i : Fin 2) : MvPolynomial (Fin 2) ℝ :=
  C (L 0 i) * scalarAffineHom a L A + C (L 1 i) * scalarAffineHom a L B

/-- The scalar curl is multiplied by the determinant under an affine
coordinate change of the base. -/
theorem scalarRowPullback_curl (a : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ)
    (A B : MvPolynomial (Fin 2) ℝ) :
    pderiv 0 (scalarRowPullback a L A B 1) -
        pderiv 1 (scalarRowPullback a L A B 0) =
      C (L 0 0 * L 1 1 - L 0 1 * L 1 0) *
        scalarAffineHom a L (pderiv 0 B - pderiv 1 A) := by
  simp only [scalarRowPullback, map_add, pderiv_C_mul, pderiv_scalarAffineHom,
    map_sub, MvPolynomial.C_sub, MvPolynomial.C_mul]
  ring

theorem scalarRowPullback_gradient (a : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    scalarRowPullback a L (pderiv 0 P) (pderiv 1 P) i =
      pderiv i (scalarAffineHom a L P) :=
  (pderiv_scalarAffineHom P a L i).symm

theorem eval_scalarRowPullback_curl_abs (a z : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ)
    (A B : MvPolynomial (Fin 2) ℝ) :
    |eval z (pderiv 0 (scalarRowPullback a L A B 1) -
        pderiv 1 (scalarRowPullback a L A B 0))| =
      |L 0 0 * L 1 1 - L 0 1 * L 1 0| *
        |eval (fun i => a i + L i 0 * z 0 + L i 1 * z 1)
          (pderiv 0 B - pderiv 1 A)| := by
  rw [scalarRowPullback_curl, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_scalarAffineHom, abs_mul]

theorem scalar_curl_bound_of_pullback (a z : Fin 2 → ℝ) (L : Fin 2 → Fin 2 → ℝ)
    (A B : MvPolynomial (Fin 2) ℝ) {κ E : ℝ} (hκ : 0 < κ)
    (hdet : κ ≤ |L 0 0 * L 1 1 - L 0 1 * L 1 0|)
    (hcurl : |eval z (pderiv 0 (scalarRowPullback a L A B 1) -
        pderiv 1 (scalarRowPullback a L A B 0))| ≤ E) :
    |eval (fun i => a i + L i 0 * z 0 + L i 1 * z 1)
      (pderiv 0 B - pderiv 1 A)| ≤ E / κ := by
  rw [eval_scalarRowPullback_curl_abs] at hcurl
  apply (le_div_iff₀ hκ).mpr
  have hm := mul_le_mul_of_nonneg_right hdet
    (abs_nonneg (eval (fun i => a i + L i 0 * z 0 + L i 1 * z 1)
      (pderiv 0 B - pderiv 1 A)))
  exact (mul_comm _ _).le.trans (hm.trans hcurl)

end Submission.Lib.K4PolynomialPotential
