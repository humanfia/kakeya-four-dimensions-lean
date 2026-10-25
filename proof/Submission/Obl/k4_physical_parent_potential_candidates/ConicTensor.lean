import Submission.Obl.k4_physical_parent_potential_candidates.FubiniAlgebra
import Submission.Lib.K4CubicTests.MatrixConditioning
import Submission.Lib.K4CubicTests.ConicMatrix
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Forms

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MvPolynomial
open scoped BigOperators

noncomputable section

namespace ConicTensor

abbrev Tensor := Fin 3 → Fin 3 → Fin 3 → ℝ

/-- The symmetric tensor of a homogeneous cubic, including its factorial. -/
def third (F : MvPolynomial (Fin 3) ℝ) (i j k : Fin 3) : ℝ :=
  (pderiv i (pderiv j (pderiv k F))).coeff 0 / 6

/-- Clear the inverse Hessian denominator in the canonical cubic defect. -/
def cleared (H : Matrix (Fin 3) (Fin 3) ℝ) (T : Tensor) (i j k : Fin 3) : ℝ :=
  5*H.det*T i j k-fubiniCubic H (fun l => ∑ a : Fin 3, ∑ b : Fin 3, H.adjugate a b*T l a b) i j k

private theorem abs_sum_three (g : Fin 3 → ℝ) {b : ℝ} (hg : ∀ i, |g i| ≤ b) :
    |∑ i, g i| ≤ 3*b := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun i _ => hg i).trans_eq (by simp))

/-- Bounded cubic coefficients bound every entry of the symmetric tensor. -/
theorem third_bound {F : MvPolynomial (Fin 3) ℝ} (hF : F.IsHomogeneous 3)
    {b : ℝ} (hb : 0 ≤ b) (hc : ∀ e, |F.coeff e| ≤ b) (i j k : Fin 3) :
    |third F i j k| ≤ b := by
  have h1 := Submission.Lib.K4CubicTests.coeff_pderiv_abs_le_of_totalDegree F 3
    hF.totalDegree_le b hb hc k
  have h2 := Submission.Lib.K4CubicTests.coeff_pderiv_abs_le_of_totalDegree (pderiv k F) 2
    (show (pderiv k F).IsHomogeneous 2 from hF.pderiv).totalDegree_le (3*b) (by positivity) h1 j
  have h3 := Submission.Lib.K4CubicTests.coeff_pderiv_abs_le_of_totalDegree (pderiv j (pderiv k F)) 1
    (show (pderiv j (pderiv k F)).IsHomogeneous 1 from hF.pderiv.pderiv).totalDegree_le
    (2*(3*b)) (by positivity) h2 i 0
  dsimp only [third]
  rw [abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 6)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ) < 6)).mpr
  norm_num at h3
  nlinarith

/-- Clearing the canonical projection costs only a cubic Hessian bound. -/
theorem cleared_bound {H : Matrix (Fin 3) (Fin 3) ℝ} {T : Tensor} {M b : ℝ}
    (hM : 0 ≤ M) (hb : 0 ≤ b) (hH : ∀ i j, |H i j| ≤ M)
    (hT : ∀ i j k, |T i j k| ≤ b) (i j k : Fin 3) :
    |cleared H T i j k| ≤ 84*M^3*b := by
  have hd := Submission.Lib.K4CubicTests.matrix_det_three_abs_le H M hM hH
  have ha := Submission.Lib.K4CubicTests.matrix_adjugate_three_abs_le H M hM hH
  have hs (l : Fin 3) : |∑ a : Fin 3, ∑ c : Fin 3, H.adjugate a c*T l a c| ≤ 18*M^2*b := by
    have ht (a c : Fin 3) : |H.adjugate a c*T l a c| ≤ 2*M^2*b := by
      rw [abs_mul]
      exact mul_le_mul (ha a c) (hT l a c) (abs_nonneg _) (by positivity)
    convert abs_sum_three (fun a => ∑ c : Fin 3, H.adjugate a c*T l a c)
      (fun a => abs_sum_three (fun c => H.adjugate a c*T l a c) (ht a)) using 1 <;> ring
  have hp (l a c : Fin 3) :
      |(∑ r : Fin 3, ∑ s : Fin 3, H.adjugate r s*T l r s)*H a c| ≤ 18*M^3*b := by
    rw [abs_mul]
    convert mul_le_mul (hs l) (hH a c) (abs_nonneg _) (by positivity) using 1 <;> ring
  have ht : |5*H.det*T i j k| ≤ 30*M^3*b := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5)]
    convert mul_le_mul_of_nonneg_left (mul_le_mul hd (hT i j k) (abs_nonneg _) (by positivity))
      (by norm_num : (0:ℝ) ≤ 5) using 1 <;> ring
  exact (abs_sub _ _).trans (by
    dsimp only [fubiniCubic]
    linarith [abs_add_le ((∑ a : Fin 3, ∑ c : Fin 3, H.adjugate a c*T i a c)*H j k)
      ((∑ a : Fin 3, ∑ c : Fin 3, H.adjugate a c*T j a c)*H i k),
      abs_add_le (((∑ a : Fin 3, ∑ c : Fin 3, H.adjugate a c*T i a c)*H j k)+
        (∑ a : Fin 3, ∑ c : Fin 3, H.adjugate a c*T j a c)*H i k)
        ((∑ a : Fin 3, ∑ c : Fin 3, H.adjugate a c*T k a c)*H i j), hp i j k, hp j i k, hp k i j])

/-- The cleared operator kills every quadratic times a linear form,
including at singular Hessians. -/
theorem adjugate_cubic_contraction (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.IsSymm) (a : Fin 3 → ℝ) (i : Fin 3) :
    (∑ j : Fin 3, ∑ k : Fin 3, H.adjugate j k*fubiniCubic H a i j k) = 5*H.det*a i := by
  calc
    _ = (∑ j : Fin 3, (H.adjugate*H) j j)*a i+
        (∑ j : Fin 3, (H.adjugate*H) j i*a j)+
        (∑ k : Fin 3, (H*H.adjugate) i k*a k) := by
      simp only [fubiniCubic, Matrix.mul_apply, Fin.sum_univ_three]
      simp only [hH.apply]
      ring
    _ = _ := by
      rw [Matrix.adjugate_mul, Matrix.mul_adjugate]
      simp [Matrix.one_apply]
      ring

theorem cleared_fubini (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (a : Fin 3 → ℝ) (i j k : Fin 3) : cleared H (fubiniCubic H a) i j k = 0 := by
  simp only [cleared, adjugate_cubic_contraction H hH]
  dsimp only [fubiniCubic]
  ring

/-- The clearing operator is linear in its tensor input. -/
theorem cleared_sub (H : Matrix (Fin 3) (Fin 3) ℝ) (S T : Tensor) (i j k : Fin 3) :
    cleared H (fun a b c => S a b c-T a b c) i j k =
      cleared H S i j k-cleared H T i j k := by
  simp only [cleared, fubiniCubic, Fin.sum_univ_three]
  ring

theorem third_sub (F G : MvPolynomial (Fin 3) ℝ) (i j k : Fin 3) :
    third (F-G) i j k = third F i j k-third G i j k := by
  simp only [third, map_sub, coeff_sub]
  ring

theorem third_quadratic_linear (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (a : Fin 3 → ℝ) (i j k : Fin 3) :
    third (Submission.Lib.K4CubicTests.matrixQuadratic H *
      Submission.Lib.K4CubicTests.linearPolynomial a) i j k =
      fubiniCubic H (fun l => a l/3) i j k := by
  have hderiv (j : Fin 3) : pderiv j (Submission.Lib.K4CubicTests.matrixQuadratic H) =
      Submission.Lib.K4CubicTests.linearPolynomial (fun k => ((2:ℝ) • H) j k) := by
    apply MvPolynomial.funext
    intro x
    rw [Submission.Lib.K4CubicTests.eval_pderiv_matrixQuadratic_symm H hH]
    simp [Submission.Lib.K4CubicTests.linearPolynomial, Matrix.mulVec, dotProduct,
      Finset.mul_sum, mul_assoc]
  rw [third, Submission.Lib.K4CubicTests.third_pderiv_quadratic_mul_linear _ _ hderiv]
  simp only [coeff_C, ite_true, Matrix.smul_apply, smul_eq_mul, fubiniCubic]
  rw [hH.apply k j, hH.apply k i, hH.apply j i]
  ring

theorem cleared_quadratic_linear (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.IsHomogeneous 1) (i j k : Fin 3) :
    cleared H (third (Submission.Lib.K4CubicTests.matrixQuadratic H * P)) i j k = 0 := by
  rw [Submission.Lib.K4CubicTests.homogeneous_one_eq_sum_linear P hP]
  change cleared H (third (Submission.Lib.K4CubicTests.matrixQuadratic H *
    Submission.Lib.K4CubicTests.linearPolynomial (fun l => (pderiv l P).coeff 0))) i j k = 0
  have ht : third (Submission.Lib.K4CubicTests.matrixQuadratic H *
      Submission.Lib.K4CubicTests.linearPolynomial (fun l => (pderiv l P).coeff 0)) =
      fubiniCubic H (fun l => (pderiv l P).coeff 0/3) := by
    funext a b c
    exact third_quadratic_linear H hH _ a b c
  rw [ht]
  exact cleared_fubini H hH _ i j k

/-- The cleared error depends only on the coefficient error modulo H times
an arbitrary homogeneous linear polynomial. -/
theorem cleared_eq_remainder (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm)
    (F P : MvPolynomial (Fin 3) ℝ) (hP : P.IsHomogeneous 1) (i j k : Fin 3) :
    cleared H (third F) i j k =
      cleared H (third (F-Submission.Lib.K4CubicTests.matrixQuadratic H*P)) i j k := by
  have ht : third (F-Submission.Lib.K4CubicTests.matrixQuadratic H*P) =
      fun a b c => third F a b c-third (Submission.Lib.K4CubicTests.matrixQuadratic H*P) a b c := by
    funext a b c
    exact third_sub _ _ a b c
  rw [ht]
  rw [cleared_sub, cleared_quadratic_linear H hH P hP, sub_zero]

/-- Scaling the Hessian scales the cleared defect by the cube. -/
theorem cleared_smul (r : ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ) (T : Tensor) (i j k : Fin 3) :
    cleared (r • H) T i j k = r^3*cleared H T i j k := by
  simp only [cleared, Matrix.det_smul, Matrix.adjugate_smul, Fintype.card_fin,
    Matrix.smul_apply, smul_eq_mul, fubiniCubic, Fin.sum_univ_three]
  ring

/-- The polynomial tensor recovers the entries of a genuine symmetric
trilinear map. -/
theorem third_formPoly
    (T : Submission.Obl.k4_approximate_conic_taylor_decomposition.E3 [×3]→L[ℝ] ℝ)
    (hT : Submission.Obl.k4_approximate_conic_taylor_decomposition.IsSymmML T)
    (i j k : Fin 3) :
    third (Submission.Obl.k4_approximate_conic_taylor_decomposition.formPoly T) i j k =
      T ![Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 i,
        Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 j,
        Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 k] := by
  open Submission.Obl.k4_approximate_conic_taylor_decomposition in
  have hp : pderiv i (pderiv j (pderiv k (formPoly T))) =
      C (6*T ![e3 k,e3 j,e3 i]) := by
    apply MvPolynomial.funext
    intro y
    rw [pderiv_formPoly T hT k, pderiv_C_mul, pderiv_C_mul, map_mul, eval_C,
      eval_pderiv_pderiv_formPoly _ (hT.curryLeft (e3 k)) i j y]
    simp only [ContinuousMultilinearMap.curryLeft_apply, eval_C]
    norm_num
    ring_nf
    congr 2
    funext a
    fin_cases a <;> rfl
  rw [third, hp]
  simp only [coeff_C, ite_true]
  have hs := hT (Equiv.swap (0:Fin 3) 2)
    ![Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 i,
      Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 j,
      Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 k]
  have he : (![Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 i,
      Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 j,
      Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 k] ∘ Equiv.swap (0:Fin 3) 2) =
      ![Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 k,
        Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 j,
        Submission.Obl.k4_approximate_conic_taylor_decomposition.e3 i] := by
    funext a
    fin_cases a <;> norm_num [Equiv.swap_apply_def]
  rw [he] at hs
  rw [hs]
  ring

end ConicTensor

end

end Submission.Obl.k4_physical_parent_potential_candidates
