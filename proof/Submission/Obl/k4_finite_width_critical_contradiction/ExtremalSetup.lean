import Submission.Obl.k4_finite_width_critical_contradiction.NarrowTerminal
import Submission.Obl.k4_finite_width_critical_contradiction.NarrownessOptimization

/-! The extremal setup and its finite optimal narrowness in exact-problem units. -/

namespace Submission.Obl.k4_finite_width_critical_contradiction

/-- An entire valid exact problem, including its infinite resolution sequence. -/
abbrev ExactProblem := {p : Data // p.Valid}

/-- Approximation refers to the outer exact problem; its resolution index is
not part of this tolerance. -/
def NearMaximizer (ds rate S η tolerance : ℝ) (p : ExactProblem) : Prop :=
  p.1.L = 1 ∧ p.1.S = S ∧ p.1.η = η ∧
    p.1.d < ds + tolerance ∧ rate - tolerance < horizon p.1

/-- The dimension, rate and relative-profile properties frozen in o119. -/
structure ExtremalSetup (ds rate S η : ℝ) : Prop where
  dimension_nonneg : 0 ≤ ds
  dimension_lt_one : ds < 1
  rate_pos : 0 < rate
  rate_le_one : rate ≤ 1
  approximants : ∀ t : ℝ, 0 < t → ∃ p : ExactProblem, NearMaximizer ds rate S η t p
  upper : ∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
    ∀ p : ExactProblem, p.1.S = S → p.1.η = η → p.1.d < ds + a →
      horizon p.1 ≤ (rate + t) * p.1.L
  profile : ∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧
    ∀ p : ExactProblem, p.1.S = S → p.1.η = η → p.1.d < ds + a →
      (rate - a) * p.1.L < horizon p.1 →
        ∀ r : ℝ, 0 ≤ r → r ≤ p.1.L → |p.1.f r - p.1.f 0 - ds * r| ≤ t * p.1.L

/-- The width and positive horizon margin are fixed before approaching
maximization. -/
def BoundedWidth (ds rate S η : ℝ) : Prop :=
  ∃ a w : ℝ, 0 < a ∧ 0 ≤ w ∧ ∀ t : ℝ, 0 < t →
    ∃ p : ExactProblem, NearMaximizer ds rate S η t p ∧
      ¬ NarrowTerminal p.1 (rate + a) w

theorem boundedWidth_iff {ds rate S η : ℝ} :
    BoundedWidth ds rate S η ↔
      ∃ w : ℝ, 0 ≤ w ∧ BoundedNarrowness (NearMaximizer ds rate S η)
        (fun p h w => NarrowTerminal p.1 h w) rate w := by
  constructor
  · rintro ⟨a, w, ha, hw, h⟩
    exact ⟨w, hw, a, ha, h⟩
  · rintro ⟨w, hw, a, ha, h⟩
    exact ⟨a, w, ha, hw, h⟩

/-- The upper horizon bound supplies the zero-width competitor uniformly over
sufficiently close exact problems. -/
theorem ExtremalSetup.uniform_zero {ds rate S η : ℝ}
    (es : ExtremalSetup ds rate S η) (hi : InitialHorizon) :
    UniformNarrowness (NearMaximizer ds rate S η)
      (fun p h w => NarrowTerminal p.1 h w) rate 0 := by
  intro margin hmargin
  obtain ⟨tolerance, htol, hupper⟩ := es.upper (margin / 2) (by positivity)
  refine ⟨tolerance, htol, fun p hp => ?_⟩
  obtain ⟨hL, hS, hη, hd, _⟩ := hp
  have hh : horizon p.1 < rate + margin := by
    have hbound := hupper p hS hη hd
    rw [hL, mul_one] at hbound
    linarith
  exact (terminal_of_horizon_lt hi p.2 hh).narrowZero p.2

/-- The finite outer optimization is performed on entire exact problems.
Every positive width error has its own bad family with a fixed horizon margin. -/
theorem ExtremalSetup.exists_optimal_width {ds rate S η : ℝ}
    (es : ExtremalSetup ds rate S η) (hi : InitialHorizon)
    (bw : BoundedWidth ds rate S η) :
    ∃ ℓ : ℝ, 0 ≤ ℓ ∧
      (∀ w, w < ℓ → UniformNarrowness (NearMaximizer ds rate S η)
        (fun p h w => NarrowTerminal p.1 h w) rate w) ∧
      (∀ ζ, 0 < ζ → UniformNarrowness (NearMaximizer ds rate S η)
        (fun p h w => NarrowTerminal p.1 h w) rate (max 0 (ℓ - ζ))) ∧
      (∀ ζ, 0 < ζ → BoundedNarrowness (NearMaximizer ds rate S η)
        (fun p h w => NarrowTerminal p.1 h w) rate (ℓ + ζ)) := by
  obtain ⟨bound, _, hbound⟩ := boundedWidth_iff.mp bw
  obtain ⟨ℓ, hℓ, _, hbelow, hlower, habove⟩ := exists_optimal_narrowness
    (NearMaximizer ds rate S η) (fun p h w => NarrowTerminal p.1 h w) rate
    (fun p _ _ _ hw h => h.mono p.2 le_rfl hw) (es.uniform_zero hi) hbound
  exact ⟨ℓ, hℓ, hbelow, hlower, habove⟩

end Submission.Obl.k4_finite_width_critical_contradiction
