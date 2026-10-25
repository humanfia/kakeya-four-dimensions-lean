import Submission.Obl.k4_scalar_candidate_original_return.ObservationCoordinates
import Submission.Obl.k4_scalar_candidate_original_return.MeshPolicy

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MvPolynomial Set

noncomputable section

def observationCoefficientPolynomial : Fin 5 → MvPolynomial (Fin 6) ℝ :=
  ![X 1 - X 0 * X 2, X 2, X 3 - X 0 * X 4 - X 0 ^ 2 * X 5, X 4, X 5]

def observationTimePolynomial : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  Fin.snoc observationCoefficientPolynomial (X 0)

lemma observationCoefficientPolynomial_degree (i : Fin 5) :
    (observationCoefficientPolynomial i).totalDegree ≤ 3 := by
  fin_cases i <;> simp only [observationCoefficientPolynomial]
  · apply k4_eligibility_sign_description.degree_sub_le (by simp)
    exact (totalDegree_mul _ _).trans (by simp)
  · simp
  · apply k4_eligibility_sign_description.degree_sub_le
    · apply k4_eligibility_sign_description.degree_sub_le (by simp)
      exact (totalDegree_mul _ _).trans (by simp)
    · exact (totalDegree_mul _ _).trans (by simp)
  all_goals simp

lemma observationTimePolynomial_degree (i : Fin 6) :
    (observationTimePolynomial i).totalDegree ≤ 3 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [observationTimePolynomial, Fin.snoc_last]
    simp
  · simpa only [observationTimePolynomial, Fin.snoc_castSucc] using
      observationCoefficientPolynomial_degree j

lemma eval_observationCoefficientPolynomial (w : Fin 6 → ℝ) :
    (fun i => MvPolynomial.eval w (observationCoefficientPolynomial i)) =
      (observationShear.symm w).1 := by
  rw [observationShear_symm_apply]
  funext i
  fin_cases i <;> simp [observationCoefficientPolynomial]

lemma eval_observationTimePolynomial (w : Fin 6 → ℝ) :
    (fun i => MvPolynomial.eval w (observationTimePolynomial i)) =
      Fin.snoc (observationShear.symm w).1 (observationShear.symm w).2 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change MvPolynomial.eval w (observationTimePolynomial (Fin.last 5)) =
        (observationShear.symm w).2
    rw [observationTimePolynomial, Fin.snoc_last]
    simp [observationShear_symm_apply]
  · simpa only [observationTimePolynomial, Fin.snoc_castSucc] using
      congrFun (eval_observationCoefficientPolynomial w) j

lemma observation_prior_format {B : ℝ} {D : ℕ} {A : Set (Fin 5 → ℝ)}
    (hB : 1 ≤ B) (hA : Format 5 B D A) :
    Format 6 B (D * 3) {w | (observationShear.symm w).1 ∈ A} := by
  have h := format_polynomial_preimage hB hA observationCoefficientPolynomial
    observationCoefficientPolynomial_degree
  simpa only [Set.preimage, eval_observationCoefficientPolynomial] using h

lemma observation_incidence_format {B : ℝ} {D : ℕ} {C : Set Inc}
    (hB : 1 ≤ B) (hC : ∀ z, Format 6 B D
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C}) (z : ℕ) :
    Format 6 B (D * 3)
      {w | ((z, (observationShear.symm w).1), (observationShear.symm w).2) ∈ C} := by
  have h := format_polynomial_preimage hB (hC z) observationTimePolynomial
    observationTimePolynomial_degree
  simpa only [Set.preimage, eval_observationTimePolynomial, mem_ofPred_eq,
    Fin.snoc_castSucc, show (5 : Fin 6) = Fin.last 5 from rfl, Fin.snoc_last] using h

/-- The terminal hidden tag is independent of the exact observed base in the
full scalar observation coordinates. -/
lemma originalObservation_in_coordinates (δ : ℝ) (q : Inc) :
    originalObservation δ q =
      (![observationShear (q.1.2, q.2) 0, observationShear (q.1.2, q.2) 1],
        ⌊observationShear (q.1.2, q.2) 3 / δ⌋) := by
  rw [observationShear_apply]
  rfl

end

end Submission.Obl.k4_scalar_candidate_original_return
