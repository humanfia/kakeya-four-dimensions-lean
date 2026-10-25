import Mathlib

namespace Submission.Obl.k4_sign_projection

/-- The sign description obtained by eliminating one real coordinate. -/
def ScalarProjection : Prop :=
  ∀ (ι η : Type) [Fintype ι] [Fintype η]
    (p : η → MvPolynomial (ι ⊕ Unit) ℝ) (B : Set (η → SignType)),
    ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ) (A : Set (Fin n → SignType)),
      ∀ x : ι → ℝ,
        (fun i => SignType.sign (MvPolynomial.eval x (q i))) ∈ A ↔
          ∃ t : ℝ,
            (fun i => SignType.sign
              (MvPolynomial.eval (Sum.elim x (fun _ : Unit => t)) (p i))) ∈ B

/-- Reindexing a finite polynomial family does not change its sign predicates. -/
theorem finite_sign_description {σ η : Type} [Fintype η]
    (p : η → MvPolynomial σ ℝ) (B : Set (η → SignType)) :
    ∃ (n : ℕ) (q : Fin n → MvPolynomial σ ℝ) (A : Set (Fin n → SignType)),
      ∀ x : σ → ℝ,
        (fun i => SignType.sign (MvPolynomial.eval x (q i))) ∈ A ↔
          (fun i => SignType.sign (MvPolynomial.eval x (p i))) ∈ B := by
  classical
  let e := Fintype.equivFin η
  refine ⟨Fintype.card η, fun i => p (e.symm i),
    {s | (fun i => s (e i)) ∈ B}, ?_⟩
  intro x
  simp only [Set.mem_ofPred_eq, Equiv.symm_apply_apply]

/-- Iterating one-coordinate elimination gives elimination of `Fin k`. -/
theorem projection_fin_of_scalar (h : ScalarProjection) (k : ℕ) :
    ∀ (ι η : Type) [Fintype ι] [Fintype η]
      (p : η → MvPolynomial (ι ⊕ Fin k) ℝ) (B : Set (η → SignType)),
      ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ) (A : Set (Fin n → SignType)),
        ∀ x : ι → ℝ,
          (fun i => SignType.sign (MvPolynomial.eval x (q i))) ∈ A ↔
            ∃ y : Fin k → ℝ,
              (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x y) (p i))) ∈ B := by
  induction k with
  | zero =>
      intro ι η _ _ p B
      let r : η → MvPolynomial ι ℝ :=
        fun i => MvPolynomial.rename (Sum.elim id Fin.elim0) (p i)
      obtain ⟨n, q, A, hA⟩ := finite_sign_description r B
      refine ⟨n, q, A, fun x => (hA x).trans ?_⟩
      have hr (y : Fin 0 → ℝ) :
          (fun i => SignType.sign (MvPolynomial.eval x (r i))) =
            (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x y) (p i))) := by
        funext i
        rw [MvPolynomial.eval_rename]
        apply congrArg (fun v => SignType.sign (MvPolynomial.eval v (p i)))
        funext j
        cases j with
        | inl j => rfl
        | inr j => exact Fin.elim0 j
      constructor
      · intro hx
        exact ⟨Fin.elim0, (hr _).symm ▸ hx⟩
      · rintro ⟨y, hy⟩
        exact hr y ▸ hy
  | succ k ih =>
      intro ι η _ _ p B
      let f : ι ⊕ Fin (k + 1) → (ι ⊕ Fin k) ⊕ Unit :=
        Sum.elim (fun i => Sum.inl (Sum.inl i))
          (Fin.cases (Sum.inr ()) (fun j => Sum.inl (Sum.inr j)))
      let r : η → MvPolynomial ((ι ⊕ Fin k) ⊕ Unit) ℝ :=
        fun i => MvPolynomial.rename f (p i)
      obtain ⟨m, q, A, hA⟩ := h (ι ⊕ Fin k) η r B
      obtain ⟨n, g, C, hC⟩ := ih ι (Fin m) q A
      refine ⟨n, g, C, fun x => (hC x).trans ?_⟩
      have hr (y : Fin k → ℝ) (t : ℝ) :
          (fun i => SignType.sign (MvPolynomial.eval
            (Sum.elim (Sum.elim x y) (fun _ : Unit => t)) (r i))) =
          (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x (Fin.cons t y)) (p i))) := by
        funext i
        rw [MvPolynomial.eval_rename]
        apply congrArg (fun v => SignType.sign (MvPolynomial.eval v (p i)))
        funext j
        cases j with
        | inl j => rfl
        | inr j =>
            refine Fin.cases ?_ (fun j => ?_) j <;> rfl
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨t, ht⟩ := (hA (Sum.elim x y)).mp hy
        exact ⟨Fin.cons t y, hr y t ▸ ht⟩
      · rintro ⟨y, hy⟩
        refine ⟨Fin.tail y, (hA _).mpr ⟨y 0, ?_⟩⟩
        rw [hr, Fin.cons_self_tail]
        exact hy

/-- The general projection theorem follows from its scalar case. -/
theorem projection_of_scalar (h : ScalarProjection) :
    ∀ (ι κ η : Type) [Fintype ι] [Fintype κ] [Fintype η]
      (p : η → MvPolynomial (ι ⊕ κ) ℝ) (B : Set (η → SignType)),
      ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ) (A : Set (Fin n → SignType)),
        ∀ x : ι → ℝ,
          (fun i => SignType.sign (MvPolynomial.eval x (q i))) ∈ A ↔
            ∃ y : κ → ℝ,
              (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x y) (p i))) ∈ B := by
  classical
  intro ι κ η _ _ _ p B
  let e := Fintype.equivFin κ
  let r : η → MvPolynomial (ι ⊕ Fin (Fintype.card κ)) ℝ :=
    fun i => MvPolynomial.rename (Sum.map id e) (p i)
  obtain ⟨n, q, A, hA⟩ := projection_fin_of_scalar h (Fintype.card κ) ι η r B
  refine ⟨n, q, A, fun x => (hA x).trans ?_⟩
  have hr (y : Fin (Fintype.card κ) → ℝ) :
      (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x y) (r i))) =
        (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x (y ∘ e)) (p i))) := by
    funext i
    rw [MvPolynomial.eval_rename]
    apply congrArg (fun v => SignType.sign (MvPolynomial.eval v (p i)))
    funext j
    cases j <;> rfl
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ∘ e, hr y ▸ hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ e.symm, ?_⟩
    rw [hr]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hy

end Submission.Obl.k4_sign_projection
