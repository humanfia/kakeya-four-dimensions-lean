import Submission.Obl.k4_scalar_tangent_isotropic_improvement.CoefficientBounds

/-! Cubic tests commute with uniform affine base changes, with their exact cubic factor. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open MvPolynomial
open scoped BigOperators

def affineBaseHom (a : Fin 2 → ℝ) (s : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
  bind₁ (fun i => C (a i) + C s * X i)

@[simp] theorem affineBaseHom_C (a : Fin 2 → ℝ) (s c : ℝ) :
    affineBaseHom a s (C c) = C c := bind₁_C_right _ _

@[simp] theorem affineBaseHom_X (a : Fin 2 → ℝ) (s : ℝ) (i : Fin 2) :
    affineBaseHom a s (X i) = C (a i) + C s * X i := bind₁_X_right _ _

theorem eval_affineBaseHom (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (s : ℝ)
    (x : Fin 2 → ℝ) : eval x (affineBaseHom a s p) = eval (fun i => a i + s * x i) p := by
  change eval₂Hom (RingHom.id ℝ) x (bind₁ _ p) = _
  rw [eval₂Hom_bind₁]
  simp only [map_add, map_mul, eval₂Hom_C, eval₂Hom_X', RingHom.id_apply]
  rfl

theorem totalDegree_affineBaseHom_le (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (s : ℝ) :
    (affineBaseHom a s p).totalDegree ≤ p.totalDegree := by
  apply Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine
  intro i
  exact (totalDegree_add _ _).trans
    (max_le (by simp) ((totalDegree_mul _ _).trans (by simp)))

theorem pderiv_affineBaseHom (p : MvPolynomial (Fin 2) ℝ) (a : Fin 2 → ℝ) (s : ℝ)
    (i : Fin 2) :
    pderiv i (affineBaseHom a s p) = C s * affineBaseHom a s (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    ring
  | mul_X p j hp =>
    by_cases hij : i = j
    · subst j
      simp [pderiv_X, hp]
      ring
    · simp [pderiv_X, Ne.symm hij, hp]
      ring

theorem thirdPartials_affineBaseHom (p : MvPolynomial (Fin 2) ℝ)
    (a : Fin 2 → ℝ) (s : ℝ) (r : Fin 4) :
    thirdPartials (affineBaseHom a s p) r = C (s ^ 3) * affineBaseHom a s (thirdPartials p r) := by
  have hthree (i j k : Fin 2) :
      pderiv i (pderiv j (pderiv k (affineBaseHom a s p))) =
      C (s ^ 3) * affineBaseHom a s (pderiv i (pderiv j (pderiv k p))) := by
    simp only [pderiv_affineBaseHom, pderiv_C_mul, map_pow]
    ring
  fin_cases r
  · exact hthree 0 0 0
  · exact hthree 0 0 1
  · exact hthree 0 1 1
  · exact hthree 1 1 1

theorem cubicTest_affineBaseHom (p : MvPolynomial (Fin 2) ℝ)
    (a x : Fin 2 → ℝ) (s v : ℝ) :
    cubicTest (affineBaseHom a s p) x v = s ^ 3 * cubicTest p (fun i => a i + s * x i) v := by
  rw [cubicTest, cubicTest, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [thirdPartials_affineBaseHom, map_mul, eval_C, eval_affineBaseHom]
  ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
