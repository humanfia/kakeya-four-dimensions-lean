/- From o050 session x0170, commit 56b4456 (branch tip e18e298).
   Integrated with the locally proved sampler and parametric Tarski queries. -/
import Mathlib

/- Adapted from x0164, commit a4470c3 of o019,
   Submission/Obl/k4_quadratic_selector_sweep/SignMoments.lean.
   The interpolation and root queries are expressed over the rationals here. -/
set_option autoImplicit false
namespace Submission.Obl.k4_sign_projection.Moments
noncomputable section
open MvPolynomial

/-- Lagrange indicator for one value of a sign coordinate. -/
def signDeltaPoly {ι : Type*} (i : ι) : SignType → MvPolynomial ι ℚ
  | .zero => 1 - X i ^ 2
  | .pos => C (1 / 2) * (X i ^ 2 + X i)
  | .neg => C (1 / 2) * (X i ^ 2 - X i)

lemma eval_signDeltaPoly {ι : Type*} (i : ι) (s : SignType) (v : ι → SignType) :
    eval (fun j => (v j : ℚ)) (signDeltaPoly i s) = if v i = s then 1 else 0 := by
  cases hs : s <;> cases hv : v i <;> norm_num [signDeltaPoly, hv]

/-- The indicator of a sign vector is polynomial on the finite sign cube. -/
def signVectorPoly {ι : Type*} [Fintype ι] (s : ι → SignType) : MvPolynomial ι ℚ :=
  ∏ i, signDeltaPoly i (s i)

lemma eval_signVectorPoly {ι : Type*} [Fintype ι] (s v : ι → SignType) :
    eval (fun i => (v i : ℚ)) (signVectorPoly s) = if v = s then 1 else 0 := by
  classical
  simp only [signVectorPoly, eval_prod, eval_signDeltaPoly]
  by_cases h : v = s
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Equality of finitely many monomial moments determines each sign-vector count. -/
theorem finite_sign_counts_of_moments {ι α β : Type*} [Fintype ι]
    (F : Finset α) (G : Finset β) (v : α → ι → SignType) (w : β → ι → SignType)
    (s : ι → SignType)
    (h : ∀ e ∈ (signVectorPoly s).support,
      ∑ x ∈ F, e.prod (fun i n => (v x i : ℚ) ^ n) =
        ∑ y ∈ G, e.prod (fun i n => (w y i : ℚ) ^ n)) :
    (F.filter (fun x => v x = s)).card = (G.filter (fun y => w y = s)).card := by
  classical
  have hm : ∑ x ∈ F, eval (fun i => (v x i : ℚ)) (signVectorPoly s) =
      ∑ y ∈ G, eval (fun i => (w y i : ℚ)) (signVectorPoly s) := by
    simp only [eval_eq]
    rw [Finset.sum_comm, Finset.sum_comm (s := G)]
    apply Finset.sum_congr rfl
    intro e he
    simpa only [← Finset.mul_sum, Finsupp.prod] using congrArg (fun z : ℚ => (signVectorPoly s).coeff e * z) (h e he)
  simp only [eval_signVectorPoly] at hm
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hm
  exact_mod_cast hm

/-- A fixed finite list of exponents suffices for all sign-vector counts. -/
def signMomentExponents (ι : Type*) [Fintype ι] : Finset (ι →₀ ℕ) := by
  classical
  exact Finset.univ.biUnion (fun s : ι → SignType => (signVectorPoly s).support)

lemma finite_sign_counts_of_fixed_moments {ι α β : Type*} [Fintype ι]
    (F : Finset α) (G : Finset β) (v : α → ι → SignType) (w : β → ι → SignType)
    (h : ∀ e ∈ signMomentExponents ι,
      ∑ x ∈ F, e.prod (fun i n => (v x i : ℚ) ^ n) =
        ∑ y ∈ G, e.prod (fun i n => (w y i : ℚ) ^ n)) (s : ι → SignType) :
    (F.filter (fun x => v x = s)).card = (G.filter (fun y => w y = s)).card := by
  classical
  exact finite_sign_counts_of_moments F G v w s (fun e he =>
    h e (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, he⟩))

end
end Submission.Obl.k4_sign_projection.Moments
