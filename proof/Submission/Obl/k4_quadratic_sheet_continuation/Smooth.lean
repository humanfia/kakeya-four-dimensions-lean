import Mathlib

/-!
# Smoothness of simple polynomial branches

We use the smooth implicit-function theorem to obtain the Fréchet derivatives
in the endpoint comparisons. This avoids requiring a several-variable
holomorphic-to-analytic theorem.
-/

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Set Filter MvPolynomial
open scoped Topology ContDiff

/-- A continuous local solution of a smooth implicit equation is smooth when
the partial derivative in the dependent variable is invertible. -/
theorem contDiffAt_of_implicit_equation
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    {k : ℕ∞ω} (hk : k ≠ 0) {P : E × F → G} {f : E → F} {a : E}
    (hP : ContDiffAt ℂ k P (a, f a)) (hf : ContinuousAt f a)
    (hroot : ∀ᶠ x in 𝓝 a, P (x, f x) = P (a, f a))
    (hD : (fderiv ℂ P (a, f a) ∘L ContinuousLinearMap.inr ℂ E F).IsInvertible) :
    ContDiffAt ℂ k f a := by
  have hpair : ContinuousAt (fun x => (x, f x)) a := continuousAt_id.prodMk hf
  have heq : f =ᶠ[𝓝 a] hP.implicitFunction hk hD := by
    filter_upwards [hpair.eventually (hP.eventually_apply_eq_iff_implicitFunction hk hD),
      hroot] with x hx hr
    exact ((hx).mp hr).symm
  exact (hP.contDiffAt_implicitFunction hk hD).congr_of_eventuallyEq heq

/-- Evaluation of a multivariate polynomial in smooth coordinate functions is smooth. -/
theorem contDiff_polynomial_eval {E σ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {k : ℕ∞ω} (P : MvPolynomial σ ℂ) (g : σ → E → ℂ)
    (hg : ∀ i, ContDiff ℂ k (g i)) :
    ContDiff ℂ k (fun x => MvPolynomial.eval (fun i => g i x) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (contDiff_const : ContDiff ℂ k (fun _ : E => c))
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | mul_X p i hp => simpa only [eval_mul, eval_X] using hp.mul (hg i)

/-- Differentiation in the last coordinate is the last polynomial partial derivative. -/
theorem hasDerivAt_eval_snoc {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ)
    (z : Fin n → ℂ) (w : ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval (Fin.snoc z t) P)
      (MvPolynomial.eval (Fin.snoc z w) (MvPolynomial.pderiv (Fin.last n) P)) w := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (hasDerivAt_const w c)
  | add p q hp hq =>
    convert hp.add hq using 1 <;> simp only [map_add] <;> rfl
  | mul_X p i hp =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · convert hp.mul (hasDerivAt_id w) using 1 <;>
        simp [pderiv_X, Fin.snoc_last, mul_comm, add_comm] <;> rfl
    · convert hp.mul (hasDerivAt_const w (z j)) using 1 <;>
        simp [pderiv_X, Fin.snoc_castSucc, mul_comm] <;> rfl

/-- The polynomial defining a graph is smooth jointly in its base and last coordinate. -/
theorem contDiff_eval_snoc {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ)
    (k : ℕ∞ω) :
    ContDiff ℂ k (fun v : EuclideanSpace ℂ (Fin n) × ℂ =>
      MvPolynomial.eval (Fin.snoc (fun j => v.1 j) v.2) P) := by
  apply contDiff_polynomial_eval P
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using
      (contDiff_snd : ContDiff ℂ k (fun v : EuclideanSpace ℂ (Fin n) × ℂ => v.2))
  · simp only [Fin.snoc_castSucc]
    fun_prop

/-- Every continuous simple branch of a polynomial equation is smooth. -/
theorem contDiffOn_simple_polynomial_root {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (P : MvPolynomial (Fin (n + 1)) ℂ)
    {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContinuousOn f U)
    (hroot : ∀ z ∈ U, MvPolynomial.eval (Fin.snoc (fun j => z j) (f z)) P = 0)
    (hsimple : ∀ z ∈ U, MvPolynomial.eval (Fin.snoc (fun j => z j) (f z))
      (MvPolynomial.pderiv (Fin.last n) P) ≠ 0) (k : ℕ∞ω) :
    ContDiffOn ℂ k f U := by
  by_cases hk : k = 0
  · subst k
    exact contDiffOn_zero.mpr hf
  intro a ha
  apply ContDiffAt.contDiffWithinAt
  let F : EuclideanSpace ℂ (Fin n) × ℂ → ℂ := fun v =>
    MvPolynomial.eval (Fin.snoc (fun j => v.1 j) v.2) P
  have hF : ContDiffAt ℂ k F (a, f a) := (contDiff_eval_snoc P k).contDiffAt
  have hpairD : HasFDerivAt (fun w : ℂ => (a, w))
      (ContinuousLinearMap.inr ℂ (EuclideanSpace ℂ (Fin n)) ℂ) (f a) := by
    convert (hasFDerivAt_const a (f a)).prodMk (hasFDerivAt_id (f a)) using 1 <;> rfl
  let d := MvPolynomial.eval (Fin.snoc (fun j => a j) (f a))
    (MvPolynomial.pderiv (Fin.last n) P)
  have hd : d ≠ 0 := hsimple a ha
  have hpartial : fderiv ℂ F (a, f a) ∘L
      ContinuousLinearMap.inr ℂ (EuclideanSpace ℂ (Fin n)) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ d := by
    apply HasFDerivAt.unique
      ((hF.hasStrictFDerivAt hk).hasFDerivAt.comp (f a) hpairD)
    exact (hasDerivAt_eval_snoc P (fun j => a j) (f a)).hasFDerivAt
  have hinv : (fderiv ℂ F (a, f a) ∘L
      ContinuousLinearMap.inr ℂ (EuclideanSpace ℂ (Fin n)) ℂ).IsInvertible := by
    rw [hpartial]
    refine ⟨(Units.mk0 d hd) • ContinuousLinearEquiv.refl ℂ ℂ, ?_⟩
    ext
    simp [mul_comm]
  apply contDiffAt_of_implicit_equation hk hF
    (hf.continuousAt (hU.mem_nhds ha)) _ hinv
  filter_upwards [hU.mem_nhds ha] with z hz
  change MvPolynomial.eval (Fin.snoc (fun j => z j) (f z)) P =
    MvPolynomial.eval (Fin.snoc (fun j => a j) (f a)) P
  rw [hroot z hz, hroot a ha]

/-- The local version of smooth polynomial substitution. -/
theorem contDiffOn_polynomial_eval {E σ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {k : ℕ∞ω} {U : Set E} (P : MvPolynomial σ ℂ) (g : σ → E → ℂ)
    (hg : ∀ i, ContDiffOn ℂ k (g i) U) :
    ContDiffOn ℂ k (fun x => MvPolynomial.eval (fun i => g i x) P) U := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (contDiffOn_const : ContDiffOn ℂ k (fun _ : E => c) U)
  | add p q hp hq => simpa only [eval_add] using hp.add hq
  | mul_X p i hp => simpa only [eval_mul, eval_X] using hp.mul (hg i)

/-- Fixed-degree evaluations of simple branches possess all the complex
Fréchet derivatives used in the continuation theorem. -/
theorem contDiffOn_sheet_evaluation {n m : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (P : Fin m → MvPolynomial (Fin (n + 1)) ℂ)
    (f : Fin m → EuclideanSpace ℂ (Fin n) → ℂ)
    (hf : ∀ i, ContinuousOn (f i) U)
    (hroot : ∀ i z, z ∈ U →
      MvPolynomial.eval (Fin.snoc (fun j => z j) (f i z)) (P i) = 0)
    (hsimple : ∀ i z, z ∈ U → MvPolynomial.eval (Fin.snoc (fun j => z j) (f i z))
      (MvPolynomial.pderiv (Fin.last n) (P i)) ≠ 0)
    (Q : MvPolynomial (Fin (n + m)) ℂ) (k : ℕ∞ω) :
    ContDiffOn ℂ k (fun z => MvPolynomial.eval
      (Fin.append (fun j : Fin n => z j) (fun i : Fin m => f i z)) Q) U := by
  apply contDiffOn_polynomial_eval Q
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    exact (by fun_prop : ContDiff ℂ k (fun z : EuclideanSpace ℂ (Fin n) => z j)).contDiffOn
  · simp only [Fin.append_right]
    exact contDiffOn_simple_polynomial_root hU (P j) (hf j)
      (hroot j) (hsimple j) k

end Submission.Obl.k4_quadratic_sheet_continuation
