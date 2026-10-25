import Mathlib
import ChallengeDeps

noncomputable section

namespace Submission.Obl.k4_scalar_marked_profile_selection

open MeasureTheory Set Filter
open scoped ENNReal

abbrev Coeff := ℕ × (Fin 5 → ℝ)
abbrev Incidence := Coeff × ℝ
abbrev Base := Fin 2 → ℝ
abbrev ObsSpace := Base × ℤ
abbrev JointSpace := ObsSpace × ℤ

abbrev Subpower (N K : ℕ → ℝ) : Prop :=
  (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

abbrev noise (σ : ℝ) : Measure (Fin 5 → ℝ) :=
  Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc 0 σ))

abbrev prior (σ : ℝ) (H : ℕ) (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) :
    Measure Coeff :=
  ∑ j, ENNReal.ofReal (w j) • Measure.map (fun u => ((j : ℕ), b j + u)) (noise σ)

abbrev event (H J : ℕ) (mark : Fin H → Fin J → Bool) : Set Incidence :=
  {p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧
    p.2 ∈ Ico ((z : ℝ) / J) (((z : ℝ) + 1) / J)}

abbrev law (σ : ℝ) (H J : ℕ) (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) : Measure Incidence :=
  ((prior σ H b w).prod volume).restrict (event H J mark)

abbrev tables (N K m : ℝ) (M H J : ℕ) (b : Fin H → Fin 5 → ℝ)
    (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) : Prop :=
  1 ≤ J ∧ (H : ℝ) ≤ N ^ (M : ℝ) ∧ (J : ℝ) ≤ N ^ (M : ℝ) ∧
  1 ≤ (J : ℝ) * N ^ (-m) ∧ (J : ℝ) * N ^ (-m) ≤ 2 ∧
  (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∀ j e, |b j e| ≤ K) ∧
  ENNReal.ofReal K⁻¹ ≤ law (N ^ (-m)) H J b w mark univ

abbrev y (l : Coeff) (t : ℝ) : ℝ := l.2 0 + t * l.2 1
abbrev x (l : Coeff) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4
abbrev obs (N r : ℝ) (p : Incidence) : ObsSpace :=
  (![p.2, y p.1 p.2], ⌊x p.1 p.2 / N ^ (-r)⌋)
abbrev aug (N r u : ℝ) (p : Incidence) : JointSpace :=
  (obs N r p, ⌊p.1.2 1 / N ^ (-u)⌋)
abbrev reference : Measure ObsSpace := volume.prod (Measure.count : Measure ℤ)
abbrev jointReference : Measure JointSpace := reference.prod (Measure.count : Measure ℤ)

abbrev raw (N K d s m S U c : ℝ) (angular : Bool) (μ : Measure Incidence) : Prop :=
  (∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : ObsSpace → ENNReal,
    Measurable g ∧ μ.map (obs N r) = reference.withDensity g ∧
      ∀ᵐ z ∂reference, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧
  (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    ∃ G : JointSpace → ENNReal, Measurable G ∧
      μ.map (aug N r u) = jointReference.withDensity G ∧
      (∀ᵐ z ∂jointReference,
        G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧
      (r = s → angular = true → 0 < u → u ≤ U →
        ∀ᵐ z ∂jointReference, G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u)))) ∧
  (∃ B : Set ObsSpace, MeasurableSet B ∧
    reference B ≤ ENNReal.ofReal (K * c⁻¹ * N ^ (d * s)) ∧
      ∀ᵐ p ∂μ, obs N s p ∈ B)

abbrev profileShape (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ r r' u : ℝ, 0 ≤ r → r ≤ r' → r' ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    0 ≤ F r' u - F r u ∧ F r' u - F r u ≤ r' - r) ∧
  (∀ r u u' : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ u' → u' ≤ 4 * (m + s + 1) →
    0 ≤ F r u' - F r u ∧ F r u' - F r u ≤ u' - u) ∧
  F s 0 = d * s - C₀ ∧
  (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    d * r - C₀ + max 0 (u - m) ≤ F r u) ∧
  (angular = true → ∀ u : ℝ, 0 ≤ u → u ≤ U → F s 0 + S * u ≤ F s u)

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

abbrev numerical (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ) : Prop :=
  F s 0 = d * s - C₀ ∧
  (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) →
    d * r - C₀ + max 0 (u - m) ≤ F r u) ∧
  (angular = true → ∀ u : ℝ, 0 ≤ u → u ≤ U → F s 0 + S * u ≤ F s u)

end Submission.Obl.k4_scalar_marked_profile_selection
