import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial Metric

noncomputable def polynomialRelation (P : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 4) ℂ := X (Fin.last 3) - rename Fin.castSucc P

lemma eval_polynomialRelation (P : MvPolynomial (Fin 3) ℂ) (x : Fin 3 → ℂ) (w : ℂ) :
    eval (Fin.snoc x w) (polynomialRelation P) = w - eval x P := by
  simp only [polynomialRelation, map_sub, eval_X, Fin.snoc_last, eval_rename]
  have hf : (Fin.snoc x w : Fin 4 → ℂ) ∘ Fin.castSucc = x := by
    funext i
    simp
  rw [hf]

lemma polynomialRelation_ne_zero (P : MvPolynomial (Fin 3) ℂ) : polynomialRelation P ≠ 0 := by
  intro h
  have he := eval_polynomialRelation P (fun _ => 0) (eval (fun _ => 0) P + 1)
  rw [h, map_zero] at he
  norm_num at he

lemma polynomialRelation_degree (P : MvPolynomial (Fin 3) ℂ) {D : ℕ}
    (hP : P.totalDegree ≤ D) : (polynomialRelation P).totalDegree ≤ max 1 D := by
  apply (totalDegree_sub _ _).trans
  apply max_le_max
  · simp
  · exact (totalDegree_rename_le _ _).trans hP

lemma polynomial_hasSheetRelation (P : MvPolynomial (Fin 3) ℂ) {D : ℕ}
    (hP : P.totalDegree ≤ D) :
    Submission.Obl.k4_algebraic_real_jet_comparison.HasSheetRelation 3 (max 1 D)
      (fun z => eval (fun i => z i) P) := by
  refine ⟨polynomialRelation P, polynomialRelation_ne_zero P, polynomialRelation_degree P hP, ?_⟩
  intro z hz
  rw [eval_polynomialRelation, sub_self]

lemma differentiable_polynomial (P : MvPolynomial (Fin 3) ℂ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 3) => eval (fun i => z i) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [eval_C]; exact differentiable_const _
  | add P Q hP hQ => simp only [eval_add]; exact hP.add hQ
  | mul_X P i hP => simp only [eval_mul, eval_X]; exact hP.mul (by fun_prop)

lemma eval_complexification (P : MvPolynomial (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    eval (fun i => ((WithLp.toLp 2 (fun j => (x j : ℂ)) : EuclideanSpace ℂ (Fin 3)) i))
        (P.map (algebraMap ℝ ℂ)) = (eval (fun i => x i) P : ℂ) := by
  rw [eval_map]
  exact (MvPolynomial.eval₂_comp (algebraMap ℝ ℂ) (fun i => x i) P).symm

lemma complexification_degree (P : MvPolynomial (Fin 3) ℝ) :
    (P.map (algebraMap ℝ ℂ)).totalDegree ≤ P.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (support_map_subset ..)

end Submission.Obl.k4_stable_native_signal_oscillation
