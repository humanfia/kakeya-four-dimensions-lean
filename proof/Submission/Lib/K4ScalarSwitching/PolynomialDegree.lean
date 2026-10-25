import Mathlib

/-!
Adapted from: here:o062
Original general degree facts: here:o028,
Submission/Obl/k4_eligibility_sign_description/Signs.lean.
These facts are exported generally because library modules cannot import obligation files.
-/

namespace Submission.Lib.K4ScalarSwitching.PolynomialDegree

variable {σ : Type*}

lemma degree_add_le {p q : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p + q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

lemma degree_sub_le {p q : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) : (p - q).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq)

lemma degree_C_mul_le (a : ℝ) (p : MvPolynomial σ ℝ) :
    (MvPolynomial.C a * p).totalDegree ≤ p.totalDegree := by
  simpa using MvPolynomial.totalDegree_mul (MvPolynomial.C a) p

lemma degree_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) : (∑ i ∈ s, f i).totalDegree ≤ d :=
  MvPolynomial.totalDegree_finsetSum_le hf

/-- Affine substitution does not increase total degree. -/
lemma degree_aeval_le {τ : Type*} (p : MvPolynomial τ ℝ)
    (f : τ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  change (MvPolynomial.C (p.coeff d) * ∏ i ∈ d.support, f i ^ d i).totalDegree ≤ p.totalDegree
  apply (degree_C_mul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hd


end Submission.Lib.K4ScalarSwitching.PolynomialDegree
