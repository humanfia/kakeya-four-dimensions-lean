-- Adapted from LOT tree g-oai-074, obligation o245, session x0931, commit 965a69347107f84b13c1c2f7a014c7386a3c7525.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/FirstJet/Statement.lean.
import Mathlib

namespace Submission.Obl.k4_fixed_prior_chart_regularization.FirstJet
open MeasureTheory

/-- The normalized scalar `x̄_l(t) = β_l + t γ_l`. -/
def xbar {Ω : Type*} (β γ : Ω → ℝ) (l : Ω) (t : ℝ) : ℝ := β l + t * γ l

/-- The scalar `S_l(t) = x̄_l(t) - F(t) · y_l`. -/
def scal {Ω : Type*} (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ) (l : Ω) (t : ℝ) :
    ℝ :=
  xbar β γ l t - (F t 0 * y l 0 + F t 1 * y l 1)

/-- The hypotheses of the first-jet cover at one resolution floor `ζ` and constant `K`. -/
structure Data {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (y : Ω → Fin 2 → ℝ)
    (β γ : Ω → ℝ) (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (d K ζ : ℝ) : Prop where
  measurable_y : Measurable y
  measurable_β : Measurable β
  measurable_γ : Measurable γ
  measurable_F : Measurable F
  measurableSet_E : MeasurableSet E
  subset_E : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1
  bound_y : ∀ l i, |y l i| ≤ K
  bound_β : ∀ l, |β l| ≤ K
  bound_γ : ∀ l, |γ l| ≤ K
  bound_F : ∀ t i, |F t i| ≤ K
  mass : ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E
  support : ∀ t q r a : ℝ, ζ ≤ q → q ≤ r → r ≤ 1 →
    ∃ C : Finset ℤ, (C.card : ℝ) ≤ K * (r / q) ^ d ∧
      ∀ l, (l, t) ∈ E → a ≤ scal y β γ F l t → scal y β γ F l t ≤ a + r →
        ⌊scal y β γ F l t / q⌋ ∈ C
  absCap : ∀ t q : ℝ, ζ ≤ q → q ≤ 1 → ∀ z : Fin 3 → ℤ,
    ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal (K * q ^ (2 + d))
  rowLip : ∀ t u : ℝ, (∃ l, (l, t) ∈ E) → (∃ l, (l, u) ∈ E) → ∀ i,
    |F t i - F u i| ≤ K * (|t - u| + ζ)
  slopeLip : ∀ l l' t u, (l, t) ∈ E → (l', u) ∈ E →
    |γ l - γ l'| ≤ K * (|t - u| + |xbar β γ l t - xbar β γ l' u| + |y l 0 - y l' 0| +
      |y l 1 - y l' 1| + ζ)
  binCap : ∀ (q : ℝ) (n : ℕ), ζ ≤ q → q ≤ (2 : ℝ) ^ (-(n : ℤ)) → ∀ (b : Fin 4 → ℤ) (t : ℝ)
    (z : Fin 3 → ℤ),
    ν {l | (⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
        ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3) ∧
        (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧ ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} ≤
      ENNReal.ofReal (K * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d)) *
        ν {l | ⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
          ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3}


end Submission.Obl.k4_fixed_prior_chart_regularization.FirstJet
