-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Basic.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory

abbrev Space := EuclideanSpace ℝ (Fin 3)

abbrev tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

abbrev FamilyHypotheses (η δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) (P : Prop) : Prop :=
  0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ Metric.ball 0 1) →
    (∀ i j, i ≠ j → volume (tube δ (x i) (v i) ∩ tube δ (x j) (v j)) ≤
      (1 / 2 : ENNReal) * volume (tube δ (x i) (v i))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (Y i) → P

abbrev EstimateE (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      FamilyHypotheses η δ n x v Y
        ((∀ U : Set Space, Convex ℝ U →
          ENNReal.ofReal ((Set.ncard {i | tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤
            ENNReal.ofReal m * volume U) →
        (∀ (u : Space) (t r : ℝ), ‖u‖ = 1 → 0 < r →
          ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆
            Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r}} : ℝ) ≤
            ENNReal.ofReal (l * n) * volume (Metric.ball 0 1 ∩ {p | |inner ℝ u p - t| ≤ r})) →
        ENNReal.ofReal (A * δ ^ (ω + ε) * m⁻¹ * (n * δ ^ 2) *
          (m ^ (-(3 / 2 : ℝ)) * l * (n * δ)) ^ (-σ)) ≤ volume (⋃ i, Y i))

abbrev prism (a b : ℝ) (c e₁ e₂ e₃ : Space) : Set Space :=
  {y | |inner ℝ e₁ (y - c)| ≤ a ∧ |inner ℝ e₂ (y - c)| ≤ b ∧
    |inner ℝ e₃ (y - c)| ≤ 1}

/-- The three counting hypotheses, retaining the exact normalization of the frozen type. -/
abbrev Factored (D b : ℝ) {n p : ℕ} (T : Fin n → Set Space)
    (P : Fin p → Set Space) : Prop :=
  (∀ i, ∃ j, T i ⊆ P j) ∧
  (∀ j j', (Set.ncard {i | T i ⊆ P j} : ℝ) ≤ D * Set.ncard {i | T i ⊆ P j'}) ∧
  (∀ U : Set Space, Convex ℝ U → ENNReal.ofReal (Set.ncard {j | P j ⊆ U}) ≤
    ENNReal.ofReal (D * p) * volume U) ∧
  (∀ j (U : Set Space), Convex ℝ U →
    ENNReal.ofReal (Set.ncard {i | T i ⊆ P j ∧ T i ⊆ U}) * volume (P j) ≤
      ENNReal.ofReal (D * Set.ncard {i | T i ⊆ P j}) * volume U) ∧
  (∀ j (U : Set Space), Convex ℝ U →
    ENNReal.ofReal (Set.ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U}) *
      volume (P j) ≤ ENNReal.ofReal D * volume U)

abbrev PrismStructure (ζ₂ ζ₃ δ : ℝ) {n : ℕ} (T : Fin n → Set Space) : Prop :=
  ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧
    ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      Factored (δ ^ (-ζ₃)) b T (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j))

abbrev Gain (σ ω ζ₂ : ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
    ∀ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₀ → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      FamilyHypotheses η δ n x v Y
        ((∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
          PrismStructure ζ₂ ζ₃ δ (fun i => tube δ (x i) (v i)) →
          ENNReal.ofReal (A * δ ^ (ω - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤
            volume (⋃ i, Y i))

/-- Proposition 5.1(B), before the quantitative aspect ratio is used. -/
abbrev AspectRatioEstimate (σ ω : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
    ∀ ζ₃ : ℝ, 0 < ζ₃ → ζ₃ ≤ ζ₀ →
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      FamilyHypotheses η δ n x v Y
        ((∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
          ∀ a b : ℝ, δ ≤ a → a ≤ b → b ≤ 1 →
          ∀ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
          (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) →
          Factored (δ ^ (-ζ₃)) b (fun i => tube δ (x i) (v i))
            (fun j => prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) →
          ENNReal.ofReal (A * δ ^ (ω + e) * (b / a) ^ ω *
            (n * δ ^ 4) ^ (σ / 2)) ≤ volume (⋃ i, Y i))

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
