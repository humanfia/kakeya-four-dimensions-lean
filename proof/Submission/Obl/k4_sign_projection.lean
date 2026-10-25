import Submission.Obl.k4_sign_projection.Projection

/-!
Finite-coordinate sign projection from shifted root sampling and
finite tests for parametric signed root queries, with proved sign interpolation.
-/

theorem Submission.k4_sign_projection : ∀ (ι κ η : Type) [Fintype ι] [Fintype κ] [Fintype η] (p : η → MvPolynomial (ι ⊕ κ) ℝ) (B : Set (η → SignType)), ∃ (n : ℕ) (q : Fin n → MvPolynomial ι ℝ) (A : Set (Fin n → SignType)), ∀ x : ι → ℝ, (fun i => SignType.sign (MvPolynomial.eval x (q i))) ∈ A ↔ ∃ y : κ → ℝ, (fun i => SignType.sign (MvPolynomial.eval (Sum.elim x y) (p i))) ∈ B :=
  Submission.Obl.k4_sign_projection.projection_of_scalar
    Submission.Obl.k4_sign_projection.scalar_projection
