import Mathlib
import ChallengeDeps

noncomputable section

namespace Submission.Obl.k4_scalar_grid_density_extension

open MeasureTheory Set Filter
open scoped ENNReal

abbrev Coeff := ℕ × (Fin 5 → ℝ)

abbrev Incidence := Coeff × ℝ

abbrev Base := Fin 2 → ℝ

abbrev ObsSpace := Base × ℤ

abbrev JointSpace := ObsSpace × ℤ

abbrev Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

abbrev y (l : Coeff) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

abbrev x (l : Coeff) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

abbrev obs (N r : ℝ) (p : Incidence) : ObsSpace :=
  (![p.2, y p.1 p.2], ⌊x p.1 p.2 / N ^ (-r)⌋)

abbrev aug (N r u : ℝ) (p : Incidence) : JointSpace :=
  (obs N r p, ⌊p.1.2 1 / N ^ (-u)⌋)

abbrev reference : Measure ObsSpace := volume.prod (Measure.count : Measure ℤ)

abbrev jointReference : Measure JointSpace := reference.prod (Measure.count : Measure ℤ)

abbrev homogeneous (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → Measure Incidence)
    (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ (g : ℕ → ℝ → ObsSpace → ENNReal) (G : ℕ → ℝ → ℝ → JointSpace → ENNReal),
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

abbrev clamp (B : ℝ) (q : ℚ) : ℝ := max 0 (min B (q : ℝ))

abbrev densityData (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → Measure Incidence)
    (g : ℕ → ℝ → ObsSpace → ENNReal)
    (G : ℕ → ℝ → ℝ → JointSpace → ENNReal) : Prop :=
  (∀ k r, 0 ≤ r → r ≤ s → Measurable (g k r) ∧
    (μ k).map (obs (N k) r) = reference.withDensity (g k r)) ∧
  (∀ k r u, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → Measurable (G k r u) ∧
    (μ k).map (aug (N k) r u) = jointReference.withDensity (G k r u))

abbrev gridData (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → Measure Incidence) : Prop :=
  ∃ (A : ℕ) (a : ℕ → ℚ → ℚ → ℝ)
    (g : ℕ → ℝ → ObsSpace → ENNReal) (G : ℕ → ℝ → ℝ → JointSpace → ENNReal),
    (∀ k q v, |a k q v| ≤ (A : ℝ)) ∧ densityData N s V μ g G ∧
    (∀ (q : ℚ) (τ : ℝ), 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      μ k {p | g k (clamp s q) (obs (N k) (clamp s q) p) <
        ENNReal.ofReal (N k ^ (-a k q 0 - τ)) ∨
        ENNReal.ofReal (N k ^ (-a k q 0 + τ)) <
          g k (clamp s q) (obs (N k) (clamp s q) p)} ≤
            ENNReal.ofReal (N k ^ (-c))) ∧
    (∀ (q v : ℚ) (τ : ℝ), 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      μ k {p | G k (clamp s q) (clamp V v)
        (aug (N k) (clamp s q) (clamp V v) p) <
          ENNReal.ofReal (N k ^ (-a k q v - τ)) ∨
        ENNReal.ofReal (N k ^ (-a k q v + τ)) <
          G k (clamp s q) (clamp V v)
            (aug (N k) (clamp s q) (clamp V v) p)} ≤
              ENNReal.ofReal (N k ^ (-c)))

abbrev regular (s V : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ s → 0 ≤ u → u ≤ V →
    0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧
  (∀ r u u' : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ u' → u' ≤ V →
    0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ u' - u)

abbrev gridExtensionStatement : Prop :=
  ∀ (N K : ℕ → ℝ) (μ : ℕ → Measure Incidence),
  (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K →
  ∀ s V : ℝ, 0 < s → 0 < V →
  (∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ μ k univ ∧ μ k univ ≤ 1) →
  gridData N s V μ →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ F : ℝ → ℝ → ℝ,
    regular s V F ∧ homogeneous (N ∘ ψ) s V (μ ∘ ψ) F

end Submission.Obl.k4_scalar_grid_density_extension
