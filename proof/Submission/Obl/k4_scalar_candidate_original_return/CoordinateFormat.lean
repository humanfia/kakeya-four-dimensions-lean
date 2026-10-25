import Submission.Obl.k4_scalar_candidate_original_return.Coordinates
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format
import Submission.Obl.k4_eligibility_sign_description.Families

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MvPolynomial Set

noncomputable section

/-- Polynomial substitution multiplies the degree bound. -/
lemma substitution_degree {n m E : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ E) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree * E := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i * E := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left (d i) (hf i))
    _ = d.sum (fun _ n => n) * E := by rw [← Finset.sum_mul]; rfl
    _ ≤ p.totalDegree * E := Nat.mul_le_mul_right E (MvPolynomial.le_totalDegree hd)

/-- Pullback does not increase the number of normalized sign tests. -/
lemma format_polynomial_preimage {n m D E : ℕ} {B : ℝ} {A : Set (Fin n → ℝ)}
    (hB : 1 ≤ B) (hA : Format n B D A)
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ E) :
    Format m B (D * E) ((fun z i => MvPolynomial.eval z (f i)) ⁻¹' A) := by
  obtain ⟨k, hk, p, hp, S, rfl⟩ := hA
  have h := k4_scalar_true_atlas_terminal_lists.Format.of_sign_family hB hk
    (fun i => MvPolynomial.aeval f (p i))
    (fun i => (substitution_degree (p i) f hf).trans (Nat.mul_le_mul_right E (hp i).1)) S
  have hset : (fun z i => MvPolynomial.eval z (f i)) ⁻¹'
      {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S} =
      {x | (fun i => SignType.sign (MvPolynomial.eval x (MvPolynomial.aeval f (p i)))) ∈ S} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq,
      k4_eligibility_sign_description.eval_aeval_real]
  rw [hset]
  exact h

/-- The inverse scalar shear is quadratic in observed-base and hidden coordinates. -/
def coefficientPolynomial : Fin 5 → MvPolynomial (Fin 6) ℝ :=
  ![X 1 - X 0 * X 2, X 2, X 3, X 4, X 5]

def coefficientTimePolynomial : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![X 1 - X 0 * X 2, X 2, X 3, X 4, X 5, X 0]

lemma coefficientPolynomial_degree (i : Fin 5) :
    (coefficientPolynomial i).totalDegree ≤ 2 := by
  fin_cases i <;> simp only [coefficientPolynomial]
  · exact k4_eligibility_sign_description.degree_sub_le (by simp)
      ((totalDegree_mul _ _).trans (by simp))
  all_goals simp

lemma coefficientTimePolynomial_degree (i : Fin 6) :
    (coefficientTimePolynomial i).totalDegree ≤ 2 := by
  fin_cases i <;> simp only [coefficientTimePolynomial]
  · exact k4_eligibility_sign_description.degree_sub_le (by simp)
      ((totalDegree_mul _ _).trans (by simp))
  all_goals simp

lemma eval_coefficientPolynomial (z : Fin 6 → ℝ) :
    (fun i => MvPolynomial.eval z (coefficientPolynomial i)) = (scalarShear.symm z).1 := by
  rw [scalarShear_symm_apply]
  funext i
  fin_cases i <;> simp [coefficientPolynomial]

lemma eval_coefficientTimePolynomial (z : Fin 6 → ℝ) :
    (fun i => MvPolynomial.eval z (coefficientTimePolynomial i)) =
      Fin.snoc (scalarShear.symm z).1 (scalarShear.symm z).2 := by
  rw [scalarShear_symm_apply]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [coefficientTimePolynomial]
  · fin_cases j <;> simp [coefficientTimePolynomial]

lemma prior_shear_format {B : ℝ} {D : ℕ} {A : Set (Fin 5 → ℝ)}
    (hB : 1 ≤ B) (hA : Format 5 B D A) :
    Format 6 B (D * 2) {z | (scalarShear.symm z).1 ∈ A} := by
  have h := format_polynomial_preimage hB hA coefficientPolynomial coefficientPolynomial_degree
  simpa only [Set.preimage, eval_coefficientPolynomial] using h

lemma incidence_shear_format {B : ℝ} {D : ℕ} {C : Set Inc}
    (hB : 1 ≤ B) (hC : ∀ z : ℕ, Format 6 B D
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C}) (z : ℕ) :
    Format 6 B (D * 2) {w | ((z, (scalarShear.symm w).1), (scalarShear.symm w).2) ∈ C} := by
  have h := format_polynomial_preimage hB (hC z) coefficientTimePolynomial
    coefficientTimePolynomial_degree
  simpa only [Set.preimage, eval_coefficientTimePolynomial, mem_ofPred_eq,
    Fin.snoc_castSucc, show (5 : Fin 6) = Fin.last 5 from rfl, Fin.snoc_last] using h

/-- Retaining a prior predicate in incidence coordinates adds no tests or degree. -/
lemma prior_incidence_format {B : ℝ} {D : ℕ} {A : Set (Fin 5 → ℝ)}
    (hB : 1 ≤ B) (hA : Format 5 B D A) :
    Format 6 B D {w | (fun e : Fin 5 => w e.castSucc) ∈ A} := by
  have h := format_polynomial_preimage hB hA
    (fun e : Fin 5 => (MvPolynomial.X e.castSucc : MvPolynomial (Fin 6) ℝ))
    (E := 1) (by intro i; simp)
  simpa only [Nat.mul_one, Set.preimage, MvPolynomial.eval_X] using h

end

end Submission.Obl.k4_scalar_candidate_original_return
