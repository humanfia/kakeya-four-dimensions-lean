import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_fixed_prior_chart_regularization

open MeasureTheory Set

variable {Ω : Type} [MeasurableSpace Ω]

/-- The affine signal in the fixed chart. -/
def xbar (β γ : Ω → ℝ) (l : Ω) (t : ℝ) : ℝ := β l + t * γ l

/-- The scalar normal signal; the prior and all four inputs remain fixed. -/
def scalar (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ)
    (l : Ω) (t : ℝ) : ℝ := xbar β γ l t - (F t 0 * y l 0 + F t 1 * y l 1)

/-- The fixed prior parameter cell at a prescribed width. -/
def coeffCell (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (r : ℝ)
    (b : Fin 4 → ℤ) : Set Ω :=
  {l | ⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧
    ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3}

/-- The instantaneous spatial cell, with a label condition. -/
def spatialCell (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (E : Set (Ω × ℝ))
    (q t : ℝ) (z : Fin 3 → ℤ) : Set Ω :=
  {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
    ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2}

/-- The mixed spatial ceilings in the input. -/
def MixedCaps (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (ζ d K : ℝ) : Prop :=
  ∀ t r w : ℝ, ζ ≤ r → r ≤ 1 → ζ ≤ w → w ≤ 1 →
    ∀ (z : Fin 2 → ℤ) (j : ℤ),
    ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / w⌋ = j ∧
      ⌊y l 0 / r⌋ = z 0 ∧ ⌊y l 1 / r⌋ = z 1} ≤
      ENNReal.ofReal (K * r ^ 2 * w ^ d)

/-- The global scalar support count in the input. -/
def ScalarSupport (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ)
    (E : Set (Ω × ℝ)) (ζ d K : ℝ) : Prop :=
  ∀ t w : ℝ, ζ ≤ w → w ≤ 1 → ∃ C : Finset ℤ,
    (C.card : ℝ) ≤ K * w ^ (-d) ∧ ∀ l, (l, t) ∈ E → ⌊scalar y β γ F l t / w⌋ ∈ C

/-- Local scalar support counts. -/
def LocalCounts (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (F : ℝ → Fin 2 → ℝ)
    (E : Set (Ω × ℝ)) (ζ d K : ℝ) : Prop :=
  ∀ t q r a : ℝ, ζ ≤ q → q ≤ r → r ≤ 1 → ∃ C : Finset ℤ,
    (C.card : ℝ) ≤ K * (r / q) ^ d ∧ ∀ l, (l, t) ∈ E →
      a ≤ scalar y β γ F l t → scalar y β γ F l t ≤ a + r →
      ⌊scalar y β γ F l t / q⌋ ∈ C

/-- The absolute instantaneous ceilings used in the output. -/
def AbsoluteCaps (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (ζ d K : ℝ) : Prop :=
  ∀ t q : ℝ, ζ ≤ q → q ≤ 1 → ∀ z : Fin 3 → ℤ,
    ν (spatialCell y β γ E q t z) ≤ ENNReal.ofReal (K * q ^ (2 + d))

/-- The row comparison on all remaining active times. -/
def RowComparison (F : ℝ → Fin 2 → ℝ) (E : Set (Ω × ℝ)) (ζ K : ℝ) : Prop :=
  ∀ t u : ℝ, (∃ l, (l, t) ∈ E) → (∃ l, (l, u) ∈ E) →
    ∀ i, |F t i - F u i| ≤ K * (|t - u| + ζ)

/-- The comparison of residual affine slopes in spacetime. -/
def SlopeComparison (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (ζ K : ℝ) : Prop :=
  ∀ l l' t u, (l, t) ∈ E → (l', u) ∈ E →
    |γ l - γ l'| ≤ K * (|t - u| + |xbar β γ l t - xbar β γ l' u| +
      |y l 0 - y l' 0| + |y l 1 - y l' 1| + ζ)

/-- The conditional ceilings keep the original, unnormalized prior cell mass. -/
def RelativeCaps (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (ζ d K : ℝ) : Prop :=
  ∀ (q : ℝ) (n : ℕ), ζ ≤ q → q ≤ (2 : ℝ) ^ (-(n : ℤ)) →
    ∀ (b : Fin 4 → ℤ) (t : ℝ) (z : Fin 3 → ℤ),
    ν (coeffCell y β γ ((2 : ℝ) ^ (-(n : ℤ))) b ∩ spatialCell y β γ E q t z) ≤
      ENNReal.ofReal (K * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d)) *
        ν (coeffCell y β γ ((2 : ℝ) ^ (-(n : ℤ))) b)

/-- The participating dyadic cells have a floor in the unchanged prior. -/
def CoeffFloors (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (ζ d H : ℝ) : Prop :=
  ∀ (n : ℕ), ζ ≤ (2 : ℝ) ^ (-(n : ℤ)) → ∀ (b : Fin 4 → ℤ),
    (∃ l t, l ∈ coeffCell y β γ ((2 : ℝ) ^ (-(n : ℤ))) b ∧ (l, t) ∈ E) →
    ENNReal.ofReal (((2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d) / H) ≤
      ν (coeffCell y β γ ((2 : ℝ) ^ (-(n : ℤ))) b)

/-- Input data, arranged in precisely the order of the frozen conjunction. -/
def Input (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ d K : ℝ) : Prop :=
  Measurable y ∧ Measurable β ∧ Measurable γ ∧ Measurable F ∧ MeasurableSet E ∧
  E ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧ (∀ l i, |y l i| ≤ K) ∧
  (∀ l, |β l| ≤ K) ∧ (∀ l, |γ l| ≤ K) ∧ (∀ t i, |F t i| ≤ K) ∧
  ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E ∧
  MixedCaps ν y β γ E ζ d K ∧ ScalarSupport y β γ F E ζ d K

/-- Output data, again in the order of the frozen conjunction. -/
def Output (ν : Measure Ω) (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ)
    (E : Set (Ω × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ d K : ℝ) : Prop :=
  Measurable y ∧ Measurable β ∧ Measurable γ ∧ Measurable F ∧ MeasurableSet E ∧
  E ⊆ univ ×ˢ Icc (0 : ℝ) 1 ∧ (∀ l i, |y l i| ≤ K) ∧
  (∀ l, |β l| ≤ K) ∧ (∀ l, |γ l| ≤ K) ∧ (∀ t i, |F t i| ≤ K) ∧
  ENNReal.ofReal K⁻¹ ≤ (ν.prod volume) E ∧ LocalCounts y β γ F E ζ d K ∧
  AbsoluteCaps ν y β γ E ζ d K ∧ RowComparison F E ζ K ∧
  SlopeComparison y β γ E ζ K ∧ RelativeCaps ν y β γ E ζ d K

end Submission.Obl.k4_fixed_prior_chart_regularization
