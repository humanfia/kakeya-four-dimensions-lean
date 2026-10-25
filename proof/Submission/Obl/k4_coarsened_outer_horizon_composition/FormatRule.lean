import Submission.Obl.k4_coarsened_outer_horizon_composition.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Set

/-- An arbitrary Boolean decision on a finite family of polynomial predicates
uses the union of their tests. Counting decisions add no polynomial degree. -/
theorem fmt_rule {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ι → ℝ)
    (hS : ∀ i, fmt n (H i) D (S i)) (rule : (ι → Prop) → Prop) :
    fmt n (∑ i, H i) D {x | rule (fun i => x ∈ S i)} := by
  classical
  choose m hm p hp b hb using hS
  let e := Fintype.equivFin (Σ i, Fin (m i))
  refine ⟨Fintype.card (Σ i, Fin (m i)), ?_,
    (fun j => p (e.symm j).1 (e.symm j).2),
    (fun j => hp (e.symm j).1 (e.symm j).2),
    (fun v => decide (rule (fun i => b i (fun j => v (e ⟨i, j⟩)) = true))), ?_⟩
  · simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hm i
  · intro x
    have hpoly (i : ι) (j : Fin (m i)) :
        p (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2 = p i j :=
      congrArg (fun z : Σ i, Fin (m i) => p z.1 z.2) (e.symm_apply_apply ⟨i, j⟩)
    simp only [mem_ofPred_eq, decide_eq_true_eq, hpoly]
    have hbits : (fun i => b i (fun j => decide (0 ≤ MvPolynomial.eval x (p i j))) = true) =
        (fun i => x ∈ S i) := by
      funext i
      exact propext (hb i x).symm
    rw [hbits]

/-- Uniformly bounded predicates give a linear test count. -/
theorem fmt_rule_uniform {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ℝ)
    (hS : ∀ i, fmt n H D (S i)) (rule : (ι → Prop) → Prop) :
    fmt n ((Fintype.card ι : ℝ) * H) D {x | rule (fun i => x ∈ S i)} := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    fmt_rule S (fun _ => H) hS rule

/-- A polynomial substitution multiplies the degree budget and leaves the
number of Boolean tests unchanged. -/
theorem fmt_polynomial_preimage {n m D d : ℕ} {H : ℝ} {S : Set (Fin n → ℝ)}
    (hS : fmt n H D S) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ d) :
    fmt m H (d * D) ((fun x i => MvPolynomial.eval x (f i)) ⁻¹' S) := by
  obtain ⟨k, hk, p, hp, b, hb⟩ := hS
  refine ⟨k, hk, fun j => MvPolynomial.aeval f (p j), fun j => ?_, b, ?_⟩
  · exact (Submission.Obl.k4_quadratic_atlas_normalization.degree_aeval_le_mul (p j) f d hf).trans
      (Nat.mul_le_mul_left d (hp j))
  · intro x
    simpa only [mem_preimage, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real] using
      hb (fun i => MvPolynomial.eval x (f i))

/-- A fixed floor label uses two polynomial comparisons, with both boundaries
encoded exactly. -/
theorem fmt_floor_eq {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) (j : ℤ) :
    fmt n 2 D {x | ⌊MvPolynomial.eval x P⌋ = j} := by
  classical
  refine ⟨2, by norm_num, ![P - MvPolynomial.C (j : ℝ), P - MvPolynomial.C ((j : ℝ) + 1)],
    ?_, (fun v => v 0 && !(v 1)), ?_⟩
  · intro i
    fin_cases i <;> apply (MvPolynomial.totalDegree_sub _ _).trans <;>
      simpa only [MvPolynomial.totalDegree_C, max_zero] using hP
  · intro x
    simp only [mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, not_le,
      map_sub, MvPolynomial.eval_C]
    rw [Int.floor_eq_iff]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

end Submission.Obl.k4_coarsened_outer_horizon_composition
