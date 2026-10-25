import Submission.Obl.k4_sign_projection.RationalCells

namespace Submission.Obl.k4_sign_projection

open Polynomial

variable {ι : Type}

/-- Specialization of a polynomial whose coefficients are parameter functions. -/
noncomputable def specialize (p : Polynomial (RFun ι)) (x : ι → ℝ) : Polynomial ℝ :=
  p.map (RFun.at x)

@[simp] lemma specialize_coeff (p : Polynomial (RFun ι)) (x : ι → ℝ) (k : ℕ) :
    (specialize p x).coeff k = RFun.at x (p.coeff k) := by
  simp [specialize]

/-- Coefficient signs determine zero status, degree, and the leading-coefficient sign. -/
lemma polynomial_data_of_coeff_signs (p q : Polynomial ℝ)
    (h : ∀ k, SignType.sign (p.coeff k) = SignType.sign (q.coeff k)) :
    (p = 0 ↔ q = 0) ∧ p.natDegree = q.natDegree ∧
      SignType.sign p.leadingCoeff = SignType.sign q.leadingCoeff := by
  have hs : p.support = q.support := by
    ext k
    rw [mem_support_iff, mem_support_iff]
    apply not_congr
    rw [← sign_eq_zero_iff, h, sign_eq_zero_iff]
  have hd : p.natDegree = q.natDegree :=
    natDegree_eq_of_degree_eq (congrArg Finset.max hs)
  refine ⟨?_, hd, ?_⟩
  · rw [← support_eq_empty, ← support_eq_empty, hs]
  · change SignType.sign (p.coeff p.natDegree) = SignType.sign (q.coeff q.natDegree)
    rw [← hd]
    exact h _

/-- All coefficient signs in a polynomial family are fixed by finitely many tests. -/
lemma specialize_coeff_signs (p : Polynomial (RFun ι)) :
    SignDetermined (fun x => fun k : Fin (p.natDegree + 1) =>
      SignType.sign ((specialize p x).coeff k)) := by
  apply SignDetermined.pi
  intro k
  simpa only [specialize_coeff] using RFun.sign (p.coeff k)

/-- Finite polynomial tests determine the specialized degree and leading-coefficient sign. -/
lemma specialize_data (p : Polynomial (RFun ι)) :
    SignDetermined (fun x => ((specialize p x).support,
      (specialize p x).natDegree, SignType.sign (specialize p x).leadingCoeff)) := by
  apply SignDetermined.of_fibers (specialize_coeff_signs p)
  intro x y hxy
  have h (k : ℕ) :
      SignType.sign ((specialize p x).coeff k) = SignType.sign ((specialize p y).coeff k) := by
    by_cases hk : k ≤ p.natDegree
    · exact congrFun hxy ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [specialize_coeff, specialize_coeff, coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk)]
      rfl
  obtain ⟨hz, hd, hl⟩ := polynomial_data_of_coeff_signs (specialize p x) (specialize p y) h
  have hs : (specialize p x).support = (specialize p y).support := by
    ext k
    rw [mem_support_iff, mem_support_iff]
    apply not_congr
    rw [← sign_eq_zero_iff, h, sign_eq_zero_iff]
  exact Prod.ext hs (Prod.ext hd hl)

end Submission.Obl.k4_sign_projection
