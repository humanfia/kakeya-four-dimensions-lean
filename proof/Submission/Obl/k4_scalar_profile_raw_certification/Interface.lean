import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds
import Submission.Obl.k4_scalar_profile_raw_certification.Profiles

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Submission.Obl.k4_scalar_profile_raw_certification

abbrev State := (ℕ × (Fin 5 → ℝ)) × ℝ
abbrev Observation := (Fin 2 → ℝ) × ℤ
abbrev JointObservation := Observation × ℤ

abbrev obs (N r : ℝ) : State → Observation :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsL (N ^ (-r))

abbrev aug (N r u : ℝ) : State → JointObservation :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.obsG (N ^ (-r)) (N ^ (-u))

abbrev reference : Measure Observation := volume.prod Measure.count
abbrev jointReference : Measure JointObservation := reference.prod Measure.count

abbrev Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

abbrev HasExponent (N c : ℕ → ℝ) (C₀ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
    N k ^ (C₀ - τ) ≤ c k ∧ c k ≤ N k ^ (C₀ + τ)

abbrev Raw (N K d s m S U c : ℝ) (angular : Bool) (μ : Measure State) : Prop :=
  (∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : Observation → ENNReal,
    Measurable g ∧ μ.map (obs N r) = reference.withDensity g ∧
      ∀ᵐ z ∂reference, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧
  (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    ∃ G : JointObservation → ENNReal,
      Measurable G ∧ μ.map (aug N r u) = jointReference.withDensity G ∧
        (∀ᵐ z ∂jointReference,
          G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧
        (r = s → angular = true → 0 < u → u ≤ U →
          ∀ᵐ z ∂jointReference, G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u)))) ∧
  (∃ B : Set Observation, MeasurableSet B ∧
    reference B ≤ ENNReal.ofReal (K * c⁻¹ * N ^ (d * s)) ∧
      ∀ᵐ p ∂μ, obs N s p ∈ B)

abbrev Homogeneous (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → Measure State)
    (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ (g : ℕ → ℝ → Observation → ENNReal)
    (G : ℕ → ℝ → ℝ → JointObservation → ENNReal),
    (∀ k r, 0 ≤ r → r ≤ s → Measurable (g k r) ∧
      (μ k).map (obs (N k) r) = reference.withDensity (g k r)) ∧
    (∀ k r u, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → Measurable (G k r u) ∧
      (μ k).map (aug (N k) r u) = jointReference.withDensity (G k r u)) ∧
    (∀ r τ : ℝ, 0 ≤ r → r ≤ s → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      μ k {p | g k r (obs (N k) r p) < ENNReal.ofReal (N k ^ (-F r 0 - τ)) ∨
        ENNReal.ofReal (N k ^ (-F r 0 + τ)) < g k r (obs (N k) r p)} ≤
          ENNReal.ofReal (N k ^ (-c))) ∧
    (∀ r u τ : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → 0 < τ →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        μ k {p | G k r u (aug (N k) r u p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨
          ENNReal.ofReal (N k ^ (-F r u + τ)) < G k r u (aug (N k) r u p)} ≤
            ENNReal.ofReal (N k ^ (-c)))

abbrev Numerical (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ) : Prop :=
  F s 0 = d * s - C₀ ∧
    (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
      d * r - C₀ + max 0 (u - m) ≤ F r u) ∧
    (angular = true → ∀ u : ℝ, 0 ≤ u → u ≤ U → F s 0 + S * u ≤ F s u)

end Submission.Obl.k4_scalar_profile_raw_certification
