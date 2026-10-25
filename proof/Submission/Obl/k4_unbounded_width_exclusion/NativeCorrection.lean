import Submission.Obl.k4_unbounded_width_exclusion.QuadraticCoefficients

noncomputable section

namespace Submission.Obl.k4_unbounded_width_exclusion

open MvPolynomial

/-- Subtracting a predictor in the observed base coordinates leaves both
native hidden-coordinate derivatives unchanged. -/
def nativeCorrection (P : MvPolynomial (Fin 4) ℝ) (F : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 4) ℝ := P - rename Fin.castSucc F

theorem pderiv_base_rename (F : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (rename Fin.castSucc F) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j, _, hj⟩ := mem_vars_rename Fin.castSucc F h
  have hjv := congrArg Fin.val hj
  have := j.isLt
  change j.val = 3 at hjv
  omega

theorem nativeCorrection_pderiv (P : MvPolynomial (Fin 4) ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (nativeCorrection P F) = pderiv (3 : Fin 4) P := by
  simp only [nativeCorrection, map_sub, pderiv_base_rename, sub_zero]

theorem nativeCorrection_pderiv_pderiv (P : MvPolynomial (Fin 4) ℝ)
    (F : MvPolynomial (Fin 3) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (nativeCorrection P F)) =
      pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P) := by
  rw [nativeCorrection_pderiv]

theorem eval_nativeCorrection (P : MvPolynomial (Fin 4) ℝ)
    (F : MvPolynomial (Fin 3) ℝ) (z : Fin 4 → ℝ) :
    eval z (nativeCorrection P F) = eval z P - eval (z ∘ Fin.castSucc) F := by
  simp [nativeCorrection, eval_rename]

theorem nativeCorrection_degree {P : MvPolynomial (Fin 4) ℝ}
    {F : MvPolynomial (Fin 3) ℝ} (hP : P.totalDegree ≤ 2) (hF : F.totalDegree ≤ 2) :
    (nativeCorrection P F).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans
    (max_le hP ((totalDegree_rename_le Fin.castSucc F).trans hF))

end Submission.Obl.k4_unbounded_width_exclusion
