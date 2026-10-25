import Mathlib

namespace Submission.Obl.k4_conditional_common_affine_field

/-- A uniform polynomial-loss version of the finite-grid construction. The same
integer exponent controls the mesh requirement, retained mass, coefficients and errors.
All input budgets have been enlarged to one number `B`. -/
def GridFieldAt (P : ℕ) : Prop :=
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsFiniteMeasure μ] (W : Set Ω)
      (t b₁ b₂ : Ω → ℝ) (F : Ω → Fin 2 → ℝ)
      (rowOpts colOpts : ℤ → Finset (Fin 3 → ℝ)) (B ω E u : ℝ),
      2 ≤ B → 0 < ω → 0 ≤ E → ω ≤ (B^P)⁻¹ →
      MeasurableSet W → Measurable t → Measurable b₁ → Measurable b₂ → Measurable F →
      B⁻¹ ≤ |u| → |u| ≤ B →
      (∀ p ∈ W, b₁ p-b₂ p=t p*u) →
      (∀ p ∈ W, |t p| ≤ 1 ∧ |b₁ p| ≤ B ∧ |b₂ p| ≤ B ∧ ∀ i, |F p i| ≤ B) →
      (∀ j, ((rowOpts j).card : ℝ) ≤ B) →
      (∀ j, ((colOpts j).card : ℝ) ≤ B) →
      (∀ j, ∀ a ∈ rowOpts j, ∀ i, |a i| ≤ B) →
      (∀ j, ∀ a ∈ colOpts j, ∀ i, |a i| ≤ B) →
      (∀ p ∈ W, ∃ a ∈ rowOpts ⌊b₁ p/ω⌋,
        |F p 0-a 0-a 1*t p| ≤ E ∧ |F p 1-a 2| ≤ E) →
      (∀ p ∈ W, ∃ a ∈ colOpts ⌊b₂ p/ω⌋,
        |F p 0-a 0-a 1*t p| ≤ E ∧ |F p 1-a 2| ≤ E) →
      (∀ i j : ℤ, μ (W ∩ {p | ⌊b₁ p/ω⌋=j ∧ ⌊b₂ p/ω⌋=i}) ≤ ENNReal.ofReal (B*ω^2)) →
      ENNReal.ofReal B⁻¹ ≤ μ W →
      ∃ (β : Fin 4 → ℝ) (c : ℝ) (T : Set Ω),
        MeasurableSet T ∧ T ⊆ W ∧ ENNReal.ofReal (B^P)⁻¹ ≤ μ T ∧
        (∀ i, |β i| ≤ B^P) ∧ |c| ≤ B^P ∧
        ∀ p ∈ T,
          |F p 0-(β 0+β 1*b₁ p+β 2*b₂ p+β 3*b₁ p*b₂ p)| ≤ B^P*(E+ω) ∧
          |F p 1-c| ≤ B^P*(E+ω)

/-- The grid step has one universal polynomial loss exponent. -/
def UniformGridField : Prop := ∃ P : ℕ, 1 ≤ P ∧ GridFieldAt P

end Submission.Obl.k4_conditional_common_affine_field
