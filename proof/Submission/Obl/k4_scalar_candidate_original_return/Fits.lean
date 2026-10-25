import Submission.Obl.k4_scalar_candidate_original_return.Defs
import Submission.Obl.k4_eligibility_sign_description.Descriptions
import Submission.Obl.k4_scalar_conditional_crop_worlds.SignFormat
import Submission.Obl.k4_scalar_conditional_crop_worlds.FormatLemmas
import Submission.Lib.K4FinitePlankAtlases.Assignments
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MvPolynomial Set
open k4_eligibility_sign_description

noncomputable section

/-- A candidate's whole-block geometric assignment, independent of analytical masks. -/
def Fit (P : Poly) (s e ε : ℝ) : Set Line :=
  {l | ∀ t ∈ Icc s e, |x l t - MvPolynomial.eval ![t, y l t] P| ≤ ε}

private def spatialSub (t : ℝ) : Fin 2 → MvPolynomial (Fin 5) ℝ :=
  ![C t, X 0 + C t * X 1]

/-- The scalar graph error at fixed time, as a polynomial in trajectory coefficients. -/
def errorPolynomial (P : Poly) (t : ℝ) : MvPolynomial (Fin 5) ℝ :=
  X 2 + C t * X 3 + C (t ^ 2) * X 4 - MvPolynomial.aeval (spatialSub t) P

lemma spatialSub_degree (t : ℝ) (i : Fin 2) : (spatialSub t i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [spatialSub]
  · change (X (0 : Fin 5) + C t * X 1).totalDegree ≤ 1
    exact degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))

lemma errorPolynomial_degree (P : Poly) (hP : P.totalDegree ≤ 2) (t : ℝ) :
    (errorPolynomial P t).totalDegree ≤ 2 := by
  apply degree_sub_le
  · exact degree_add_le (degree_add_le (by simp)
      ((degree_C_mul_le _ _).trans (by simp)))
      ((degree_C_mul_le _ _).trans (by simp))
  · exact (degree_aeval_le P (spatialSub t) (spatialSub_degree t)).trans hP

lemma eval_errorPolynomial (P : Poly) (t : ℝ) (a : Fin 5 → ℝ) (z : ℕ) :
    MvPolynomial.eval a (errorPolynomial P t) =
      x (z, a) t - MvPolynomial.eval ![t, y (z, a) t] P := by
  have hsub : (fun i => MvPolynomial.eval a (spatialSub t i)) = ![t, y (z, a) t] := by
    funext i
    fin_cases i <;> simp [spatialSub, y, k4_scalar_linear_critical_extremizers.Split.y]
  simp only [errorPolynomial, map_sub, map_add, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_C, eval_aeval_real, hsub]
  rfl

lemma quadratic_error (P : Poly) (hP : P.totalDegree ≤ 2) (a : Fin 5 → ℝ) :
    Quadratic (fun t => MvPolynomial.eval a (errorPolynomial P t)) := by
  have hp := Quadratic.mv_line P hP (![0, a 0] : Fin 2 → ℝ) ![1, a 1]
  have heq (t : ℝ) : (fun i => (![0, a 0] : Fin 2 → ℝ) i +
      t * (![1, a 1] : Fin 2 → ℝ) i) = ![t, y (0, a) t] := by
    funext i
    fin_cases i <;> simp [y, k4_scalar_linear_critical_extremizers.Split.y]
  obtain ⟨A, B, C, hp⟩ := hp
  dsimp only at hp
  refine ⟨a 4 - A, a 3 - B, a 2 - C, fun t => ?_⟩
  dsimp only
  rw [eval_errorPolynomial P t a 0, ← heq t, hp]
  dsimp [x, k4_scalar_linear_critical_extremizers.Split.x]
  ring

lemma Fit_format (P : Poly) (hP : P.totalDegree ≤ 2) (s e ε : ℝ) (hse : s ≤ e)
    (z : ℕ) : Format 5 12 4 {a | (z, a) ∈ Fit P s e ε} := by
  have h := SignRep.quadratic_abs_family (id : (Fin 5 → ℝ) → Fin 5 → ℝ) false
    (errorPolynomial P) (errorPolynomial_degree P hP) (quadratic_error P hP) ε s e hse
  apply k4_scalar_conditional_crop_worlds.format_of_signRep (k := 12) (by norm_num) (by norm_num)
  simpa only [Fit, id_eq, Bool.false_eq_true, ↓reduceIte, mem_ofPred_eq,
    eval_errorPolynomial P _ _ z] using h

lemma Fit_closed (P : Poly) (s e ε : ℝ) : IsClosed (Fit P s e ε) := by
  have heq : Fit P s e ε = ⋂ t ∈ Icc s e,
      {l | |x l t - MvPolynomial.eval ![t, y l t] P| ≤ ε} := by
    ext l
    simp [Fit]
  rw [heq]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro ht
  apply isClosed_le ?_ continuous_const
  apply Continuous.abs
  apply Continuous.sub
  · dsimp [x, k4_scalar_linear_critical_extremizers.Split.x]
    fun_prop
  · apply (MvPolynomial.continuous_eval P).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · dsimp [y, k4_scalar_linear_critical_extremizers.Split.y]
      fun_prop

/-- Finite candidate priority rules retain uniformly bounded polynomial format. -/
lemma priority_Fit_format {n : ℕ} (P : Fin n → Poly) (hP : ∀ i, (P i).totalDegree ≤ 2)
    (s e ε : ℝ) (hse : s ≤ e) (i : Fin n) (z : ℕ) :
    Format 5 (12 * ((n : ℝ) + 1)) 4
      {a | (z, a) ∈ Submission.Lib.K4FinitePlankAtlases.firstAssignment
        (fun j => Fit (P j) s e ε) i} := by
  classical
  let S : Fin n → Set (Fin 5 → ℝ) := fun j =>
    if j < i then {a | (z, a) ∈ Fit (P j) s e ε}ᶜ else univ
  have hS (j : Fin n) : Format 5 12 4 (S j) := by
    dsimp only [S]
    split
    · exact k4_scalar_true_atlas_terminal_lists.Format.compl (Fit_format (P j) (hP j) s e ε hse z)
    · exact k4_scalar_conditional_crop_worlds.Format.univ 5 (by norm_num) 4
  have h := k4_scalar_conditional_crop_worlds.Format.inter
    (Fit_format (P i) (hP i) s e ε hse z)
    (k4_scalar_conditional_crop_worlds.Format.iInter_fin (by norm_num) n S hS)
  have heq : {a | (z, a) ∈ Submission.Lib.K4FinitePlankAtlases.firstAssignment
      (fun j => Fit (P j) s e ε) i} = {a | (z, a) ∈ Fit (P i) s e ε} ∩ ⋂ j, S j := by
    ext a
    simp [Submission.Lib.K4FinitePlankAtlases.firstAssignment, S]
  rw [heq, show 12 * ((n : ℝ) + 1) = 12 + (n : ℝ) * 12 by ring]
  exact h

end

end Submission.Obl.k4_scalar_candidate_original_return
