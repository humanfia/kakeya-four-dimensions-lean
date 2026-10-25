/- From o050 session x0170, commit 56b4456 (branch tip e18e298).
   Integrated with the locally proved sampler and parametric Tarski queries. -/
import Submission.Obl.k4_sign_projection.Sampling
import Submission.Obl.k4_sign_projection.Iteration

noncomputable section

namespace Submission.Obl.k4_sign_projection

open scoped BigOperators Classical

/-- A predicate constant on the cells of a finite polynomial sign map has a
finite sign description. -/
theorem description_of_invariant {ι α : Type} [Fintype α]
    (q : α → MvPolynomial ι ℝ) (R : (ι → ℝ) → Prop)
    (h : ∀ x y, (∀ i, SignType.sign (MvPolynomial.eval x (q i)) =
      SignType.sign (MvPolynomial.eval y (q i))) → (R x ↔ R y)) :
    ∃ (n : ℕ) (g : Fin n → MvPolynomial ι ℝ) (A : Set (Fin n → SignType)),
      ∀ x, (fun i => SignType.sign (MvPolynomial.eval x (g i))) ∈ A ↔ R x := by
  let C : Set (α → SignType) :=
    {s | ∃ y, R y ∧ ∀ i, s i = SignType.sign (MvPolynomial.eval y (q i))}
  obtain ⟨n, g, A, hA⟩ := finite_sign_description q C
  refine ⟨n, g, A, fun x => (hA x).trans ?_⟩
  change (∃ y, R y ∧ ∀ i, SignType.sign (MvPolynomial.eval x (q i)) =
    SignType.sign (MvPolynomial.eval y (q i))) ↔ R x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (h x y hxy).mpr hy
  · intro hx
    exact ⟨x, hx, fun _ => rfl⟩

/-- Isolate the one fibre coordinate as a univariate indeterminate. -/
def asUnivariate {ι : Type} (p : MvPolynomial (ι ⊕ Unit) ℝ) :
    Polynomial (MvPolynomial ι ℝ) :=
  MvPolynomial.optionEquivLeft ℝ ι
    (MvPolynomial.rename (Sum.elim some (fun _ : Unit => none)) p)

/-- This coordinate identification commutes with real evaluation. -/
@[simp] theorem eval_asUnivariate {ι : Type} (x : ι → ℝ) (t : ℝ)
    (p : MvPolynomial (ι ⊕ Unit) ℝ) :
    (specializePoly x (asUnivariate p)).eval t =
      MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) p := by
  unfold specializePoly asUnivariate
  rw [← MvPolynomial.optionEquivLeft_elim_eval, MvPolynomial.eval_rename]
  apply congrArg (fun v => MvPolynomial.eval v p)
  funext i
  cases i <;> rfl

@[simp] theorem specialize_exponentProduct {ι η : Type} [Fintype η]
    (x : ι → ℝ) (p : η → Polynomial (MvPolynomial ι ℝ)) (e : η →₀ ℕ) :
    specializePoly x (e.prod (fun i n => p i ^ n)) =
      e.prod (fun i n => specializePoly x (p i) ^ n) := by
  simp [specializePoly, Finsupp.prod, Polynomial.map_prod]

/-- Root sampling and finite parametric query tests imply elimination of one real coordinate. -/
theorem scalar_projection : ScalarProjection := by
  classical
  intro ι η _ _ p B
  let P : η → Polynomial (MvPolynomial ι ℝ) := fun i => asUnivariate (p i)
  let J := Finset η × {e : η →₀ ℕ // e ∈ Moments.signMomentExponents η}
  let f : J → Polynomial (MvPolynomial ι ℝ) := fun j => samples P j.1
  let g : J → Polynomial (MvPolynomial ι ℝ) := fun j => j.2.val.prod (fun i n => P i ^ n)
  obtain ⟨n, q, hq⟩ := exists_simultaneous_query_tests f g
  let Q : (Σ j : J, Fin (n j)) → MvPolynomial ι ℝ := fun a => q a.1 a.2
  let R : (ι → ℝ) → Prop :=
    fun x => ∃ t, signsAt (fun i => specializePoly x (P i)) t ∈ B
  have hR (x y : ι → ℝ)
      (hxy : ∀ a, SignType.sign (MvPolynomial.eval x (Q a)) =
        SignType.sign (MvPolynomial.eval y (Q a))) : R x ↔ R y := by
    have hqueries (S : Finset η) (e : η →₀ ℕ) (he : e ∈ Moments.signMomentExponents η) :
        rootQuery (samples (fun i => specializePoly x (P i)) S)
          (e.prod (fun i n => specializePoly x (P i) ^ n)) =
        rootQuery (samples (fun i => specializePoly y (P i)) S)
          (e.prod (fun i n => specializePoly y (P i) ^ n)) := by
      simpa only [f, g, specialize_samples, specialize_exponentProduct] using
        hq x y (fun j k => hxy ⟨j, k⟩) (S, ⟨e, he⟩)
    change (∃ t, signsAt (fun i => specializePoly x (P i)) t ∈ B) ↔
      ∃ t, signsAt (fun i => specializePoly y (P i)) t ∈ B
    rw [feasible_iff_samples, feasible_iff_samples]
    apply exists_congr
    intro S
    exact exists_root_signs_iff_of_queries _ _ _ _ B (hqueries S)
  obtain ⟨m, q', A, hA⟩ := description_of_invariant Q R hR
  refine ⟨m, q', A, fun x => (hA x).trans ?_⟩
  change (∃ t, (fun i => SignType.sign
    ((specializePoly x (asUnivariate (p i))).eval t)) ∈ B) ↔ _
  simp only [eval_asUnivariate]

end Submission.Obl.k4_sign_projection
