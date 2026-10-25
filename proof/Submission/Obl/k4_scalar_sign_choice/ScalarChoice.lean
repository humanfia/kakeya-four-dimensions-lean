/- Adapted from this LOT tree, obligation o029, session x0089, commits
2c6ac76 and 18abde3, file Submission/Obl/k4_bounded_sign_choice/ScalarChoice.lean.
Namespace and imports changed to the owned o051 module. -/

import Submission.Obl.k4_scalar_sign_choice.SignDefinable
import Submission.Obl.k4_scalar_sign_choice.FiniteSamples

namespace Submission.Obl.k4_scalar_sign_choice

open MvPolynomial Set

theorem sum_scalar_eta {ι : Type} (z : (ι ⊕ Unit) → ℝ) :
    Sum.elim (fun i => z (Sum.inl i)) (fun _ => z (Sum.inr ())) = z := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i; rfl

theorem sum_scalar_comp {ι κ : Type} (x : (ι ⊕ Unit) → ℝ) (y : κ → ℝ) (j : κ) :
    Sum.elim x y ∘ (Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ : Unit => Sum.inr j)) =
      Sum.elim (fun i => x (Sum.inl i)) (fun _ => y j) := by
  funext i
  cases i <;> rfl

/-- A polynomial with the base coordinates fixed and the scalar coordinate
retained as a univariate indeterminate. -/
noncomputable def fiberPolynomial {ι : Type} (p : MvPolynomial (ι ⊕ Unit) ℝ)
    (x : ι → ℝ) : Polynomial ℝ :=
  eval₂ Polynomial.C (Sum.elim (fun i => Polynomial.C (x i)) (fun _ => Polynomial.X)) p

theorem eval_fiberPolynomial {ι : Type} (p : MvPolynomial (ι ⊕ Unit) ℝ)
    (x : ι → ℝ) (t : ℝ) :
    (fiberPolynomial p x).eval t = eval (Sum.elim x (fun _ => t)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [fiberPolynomial]
  | add p q hp hq => simpa [fiberPolynomial, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p j hp =>
    cases j <;> simp_all [fiberPolynomial, eval₂_mul]

theorem fiberPolynomial_ne_zero_iff {ι : Type} (p : MvPolynomial (ι ⊕ Unit) ℝ)
    (x : ι → ℝ) :
    fiberPolynomial p x ≠ 0 ↔ ∃ t, eval (Sum.elim x (fun _ => t)) p ≠ 0 := by
  simp_rw [← eval_fiberPolynomial]
  constructor
  · contrapose!
    exact Polynomial.zero_of_eval_zero _
  · rintro ⟨t, ht⟩ h
    simp [h] at ht

theorem SignDefinable.fiber_nonzero (hproj : SignProjection) {ι : Type} [Fintype ι]
    (p : MvPolynomial (ι ⊕ Unit) ℝ) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ =>
      ∃ t, eval (Sum.elim (fun i => z (Sum.inl i)) (fun _ => t)) p ≠ 0) := by
  let f : (ι ⊕ Unit) → ((ι ⊕ Unit) ⊕ Unit) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ())
  have h := ((SignDefinable.polynomial_eq p 0).not.coordinate_precomp f).exists_real hproj
  simpa only [f, sum_scalar_comp, map_zero] using h

theorem SignDefinable.fiber_roots (hproj : SignProjection) {ι η : Type}
    [Fintype ι] [Fintype η] (p : η → MvPolynomial (ι ⊕ Unit) ℝ) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ => z (Sum.inr ()) ∈
      familyRoots (fun i => fiberPolynomial (p i) (fun j => z (Sum.inl j)))) := by
  apply (SignDefinable.ex_finite (fun i =>
    (SignDefinable.fiber_nonzero hproj (p i)).and (SignDefinable.polynomial_eq (p i) 0))).congr
  intro z
  simp only [familyRoots, Set.mem_ofPred_eq, fiberPolynomial_ne_zero_iff,
    eval_fiberPolynomial, map_zero, sum_scalar_eta]

/-- A fixed polynomial translation of a root predicate, retaining the base. -/
theorem SignDefinable.root_shift (hproj : SignProjection) {ι : Type} [Fintype ι]
    {R : ((ι ⊕ Unit) → ℝ) → Prop} (hR : SignDefinable R) (c : ℝ) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ =>
      ∃ a, R (Sum.elim (fun i => z (Sum.inl i)) (fun _ => a)) ∧
        z (Sum.inr ()) = a + c) := by
  let f : (ι ⊕ Unit) → ((ι ⊕ Unit) ⊕ Unit) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ())
  have h := ((hR.coordinate_precomp f).and
    (SignDefinable.polynomial_eq (X (Sum.inl (Sum.inr ()))) (X (Sum.inr ()) + C c)))
      |>.exists_real hproj
  simpa only [f, sum_scalar_comp, Sum.elim_inl, Sum.elim_inr, eval_X, map_add, eval_C] using h

theorem SignDefinable.root_midpoint (hproj : SignProjection) {ι : Type} [Fintype ι]
    {R : ((ι ⊕ Unit) → ℝ) → Prop} (hR : SignDefinable R) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ =>
      ∃ a b, R (Sum.elim (fun i => z (Sum.inl i)) (fun _ => a)) ∧
        R (Sum.elim (fun i => z (Sum.inl i)) (fun _ => b)) ∧
        z (Sum.inr ()) = (a + b) / 2) := by
  let fa : (ι ⊕ Unit) → ((ι ⊕ Unit) ⊕ Fin 2) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr 0)
  let fb : (ι ⊕ Unit) → ((ι ⊕ Unit) ⊕ Fin 2) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr 1)
  have h := ((hR.coordinate_precomp fa).and ((hR.coordinate_precomp fb).and
    (SignDefinable.polynomial_eq (X (Sum.inl (Sum.inr ())))
      ((X (Sum.inr 0) + X (Sum.inr 1)) * C (1 / 2))))).exists_block hproj
  apply h.congr
  intro z
  simp only [fa, fb, sum_scalar_comp, Sum.elim_inl, Sum.elim_inr, eval_X, map_add,
    eval_C, map_mul, mul_one_div]
  constructor
  · rintro ⟨v, ha, hb, ht⟩
    exact ⟨v 0, v 1, ha, hb, ht⟩
  · rintro ⟨a, b, ha, hb, ht⟩
    exact ⟨![a, b], ha, hb, ht⟩

theorem SignDefinable.root_samples (hproj : SignProjection) {ι : Type} [Fintype ι]
    {R : ((ι ⊕ Unit) → ℝ) → Prop} (hR : SignDefinable R) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ => z (Sum.inr ()) ∈
      rootSamples {t | R (Sum.elim (fun i => z (Sum.inl i)) (fun _ => t))}) := by
  have hz : SignDefinable (fun z : (ι ⊕ Unit) → ℝ => z (Sum.inr ()) = 0) := by
    simpa only [eval_X, map_zero] using SignDefinable.polynomial_eq (X (Sum.inr ())) 0
  apply ((((hz.or hR).or (hR.root_shift hproj 1)).or
    (hR.root_shift hproj (-1))).or (hR.root_midpoint hproj)).congr
  intro z
  simp only [rootSamples, mem_union, mem_singleton_iff, mem_image, mem_prod,
    Set.mem_ofPred_eq]
  have hbase : Sum.elim (fun i => z (Sum.inl i)) (fun _ => z (Sum.inr ())) = z := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => cases j; rfl
  rw [hbase]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · rcases h with ⟨a, ha, ht⟩
      exact Or.inl (Or.inl (Or.inr ⟨a, ha, ht.symm⟩))
    · rcases h with ⟨a, ha, ht⟩
      exact Or.inl (Or.inr ⟨a, ha, by linarith⟩)
    · rcases h with ⟨a, b, ha, hb, ht⟩
      exact Or.inr ⟨(a, b), ⟨ha, hb⟩, ht.symm⟩
  · rintro ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · rcases h with ⟨a, ha, ht⟩
      exact Or.inl (Or.inl (Or.inr ⟨a, ha, ht.symm⟩))
    · rcases h with ⟨a, ha, ht⟩
      exact Or.inl (Or.inr ⟨a, ha, by linarith⟩)
    · rcases h with ⟨⟨a, b⟩, ⟨ha, hb⟩, ht⟩
      exact Or.inr ⟨a, b, ha, hb, ht.symm⟩

theorem SignDefinable.least_member (hproj : SignProjection) {ι : Type} [Fintype ι]
    {P : ((ι ⊕ Unit) → ℝ) → Prop} (hP : SignDefinable P) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ => P z ∧
      ∀ u, P (Sum.elim (fun i => z (Sum.inl i)) (fun _ => u)) → z (Sum.inr ()) ≤ u) := by
  let f : (ι ⊕ Unit) → ((ι ⊕ Unit) ⊕ Unit) :=
    Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ())
  have h := ((hP.coordinate_precomp f).imp
    (SignDefinable.polynomial_le (X (Sum.inl (Sum.inr ()))) (X (Sum.inr ()))))
    |>.forall_real hproj
  apply (hP.and h).congr
  intro z
  simp only [f, sum_scalar_comp, eval_X, Sum.elim_inl, Sum.elim_inr]

theorem SignDefinable.sample_choice_graph (hproj : SignProjection) {ι η : Type}
    [Fintype ι] [Fintype η] (p : η → MvPolynomial (ι ⊕ Unit) ℝ)
    (B : Set (η → SignType)) :
    SignDefinable (fun z : (ι ⊕ Unit) → ℝ =>
      sampleChoiceGraph (fun i => fiberPolynomial (p i) (fun j => z (Sum.inl j))) B
        (z (Sum.inr ()))) := by
  have hroots := SignDefinable.fiber_roots hproj p
  have hsamples := hroots.root_samples hproj
  have hsign := SignDefinable.of_family p B
  have h := (hsign.and hsamples).least_member hproj
  apply h.congr
  intro z
  simp only [sampleChoiceGraph, eval_fiberPolynomial, sum_scalar_eta, Sum.elim_inl,
    Sum.elim_inr, Set.ofPred_mem_eq, and_imp, and_assoc]

/-- A canonical scalar selector; existence and uniqueness are proved by the
finite sample argument, independently of projection. -/
noncomputable def scalarSelector {ι η : Type} [Finite η]
    (p : η → MvPolynomial (ι ⊕ Unit) ℝ) (B : Set (η → SignType)) (x : ι → ℝ) : ℝ := by
  classical
  let q := fun i => fiberPolynomial (p i) x
  exact if h : ∃ t, (fun i => SignType.sign ((q i).eval t)) ∈ B then
    (exists_unique_sampleChoice q B h).exists.choose else 0

theorem scalarSelector_spec {ι η : Type} [Finite η]
    (p : η → MvPolynomial (ι ⊕ Unit) ℝ) (B : Set (η → SignType)) (x : ι → ℝ)
    (hx : ∃ t, (fun i => SignType.sign (eval (Sum.elim x (fun _ => t)) (p i))) ∈ B) :
    sampleChoiceGraph (fun i => fiberPolynomial (p i) x) B (scalarSelector p B x) := by
  have hx' : ∃ t, (fun i => SignType.sign ((fiberPolynomial (p i) x).eval t)) ∈ B := by
    simpa only [eval_fiberPolynomial] using hx
  simp only [scalarSelector, dite_eq_left hx']
  exact (exists_unique_sampleChoice _ B hx').exists.choose_spec

theorem sampleChoiceGraph_iff {ι η : Type} [Finite η]
    (p : η → MvPolynomial (ι ⊕ Unit) ℝ) (B : Set (η → SignType)) (x : ι → ℝ) (t : ℝ) :
    sampleChoiceGraph (fun i => fiberPolynomial (p i) x) B t ↔
      (∃ u, (fun i => SignType.sign (eval (Sum.elim x (fun _ => u)) (p i))) ∈ B) ∧
      scalarSelector p B x = t := by
  constructor
  · intro ht
    have hx : ∃ u, (fun i => SignType.sign (eval (Sum.elim x (fun _ => u)) (p i))) ∈ B :=
      ⟨t, by simpa only [eval_fiberPolynomial] using ht.1⟩
    have hsel := scalarSelector_spec p B x hx
    refine ⟨hx, ?_⟩
    exact le_antisymm (hsel.2.2 t ht.1 ht.2.1) (ht.2.2 _ hsel.1 hsel.2.1)
  · rintro ⟨hx, heq⟩
    rw [← heq]
    exact scalarSelector_spec p B x hx

/-- Qualitative scalar semialgebraic choice, with projection as its sole
additional mathematical input. -/
theorem scalar_choice_of_projection (hproj : SignProjection) :
    ∀ (ι η : Type) [Fintype ι] [Fintype η]
      (p : η → MvPolynomial (ι ⊕ Unit) ℝ) (B : Set (η → SignType)),
      ∃ (b : (ι → ℝ) → ℝ) (n : ℕ) (g : Fin n → MvPolynomial (ι ⊕ Unit) ℝ)
        (A : Set (Fin n → SignType)),
        (∀ (x : ι → ℝ) (t : ℝ),
          (fun i => SignType.sign (eval (Sum.elim x (fun _ : Unit => t)) (g i))) ∈ A ↔
          (∃ u : ℝ, (fun i => SignType.sign (eval (Sum.elim x (fun _ : Unit => u))
            (p i))) ∈ B) ∧ b x = t) ∧
        (∀ x : ι → ℝ,
          (∃ u : ℝ, (fun i => SignType.sign (eval (Sum.elim x (fun _ : Unit => u))
            (p i))) ∈ B) →
          (fun i => SignType.sign (eval (Sum.elim x (fun _ : Unit => b x)) (p i))) ∈ B) := by
  intro ι η _ _ p B
  obtain ⟨n, g, A, hgraph⟩ := SignDefinable.sample_choice_graph hproj p B
  refine ⟨scalarSelector p B, n, g, A, ?_, ?_⟩
  · intro x t
    exact (hgraph (Sum.elim x (fun _ => t))).symm.trans (sampleChoiceGraph_iff p B x t)
  · intro x hx
    have h := (scalarSelector_spec p B x hx).1
    simpa only [eval_fiberPolynomial] using h

end Submission.Obl.k4_scalar_sign_choice
