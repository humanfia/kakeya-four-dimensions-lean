-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PrismInterface.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PrismInterface.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory

/-- The Frostman specialization of the general-prism estimate. -/
abbrev PrismFrostmanEstimate (σ ω : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 → s ≤ d₀ →
  ∀ (n : ℕ) (P Z : Fin n → Set Space) (c e₁ e₂ e₃ : Fin n → Space),
  0 < n → (∀ i, Orthonormal ℝ ![e₁ i, e₂ i, e₃ i]) →
  (∀ i, Convex ℝ (P i)) → (∀ i, MeasurableSet (P i)) →
  (∀ i, {y | |inner ℝ (e₁ i) (y - c i)| ≤ s / 10 ∧
    |inner ℝ (e₂ i) (y - c i)| ≤ t / 10 ∧
    |inner ℝ (e₃ i) (y - c i)| ≤ (1 / 10 : ℝ)} ⊆ P i) →
  (∀ i, P i ⊆ {y | |inner ℝ (e₁ i) (y - c i)| ≤ 10 * s ∧
    |inner ℝ (e₂ i) (y - c i)| ≤ 10 * t ∧
    |inner ℝ (e₃ i) (y - c i)| ≤ (10 : ℝ)}) →
  (∀ i, P i ⊆ Metric.ball 0 10) →
  (∀ i j, i ≠ j → volume (P i ∩ P j) ≤
    (1 / 2 : ENNReal) * volume (P i)) →
  (∀ i, MeasurableSet (Z i)) → (∀ i, Z i ⊆ P i) →
  ENNReal.ofReal (s ^ η * n * s * t) ≤ ∑ i, volume (Z i) →
  (∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal (Set.ncard {i | P i ⊆ U}) ≤
      ENNReal.ofReal (s ^ (-η) * n) * volume U) →
  (∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal (Set.ncard {i | P i ⊆ U}) * ENNReal.ofReal ((s * t) ^ 2) ≤
      ENNReal.ofReal (s ^ (-η)) * (volume U) ^ 2) →
  ENNReal.ofReal (A * s ^ e * t ^ ω * (n * (s * t) ^ 2) ^ (σ / 2)) ≤
    volume (⋃ i, Z i)

/-- The local planar L2 input, uniformly in the prism position and frame. -/
abbrev LocalThickeningDensity : Prop :=
  ∀ e : ℝ, 0 < e → ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
  ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ δ a b : ℝ, 0 < δ → δ ≤ d₀ →
  δ ≤ a → a ≤ b → b ≤ 1 →
  ∀ (c e₁ e₂ e₃ : Space), Orthonormal ℝ ![e₁, e₂, e₃] →
  ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
  0 < n → (∀ i, ‖v i‖ = 1) →
  (∀ i, tube δ (x i) (v i) ⊆ prism a b c e₁ e₂ e₃) →
  (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
  (∀ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (Y i)) →
  (∀ U : Set Space, Convex ℝ U →
    ENNReal.ofReal (Set.ncard {i | tube δ (x i) (v i) ⊆ U}) *
      volume (prism a b c e₁ e₂ e₃) ≤
    ENNReal.ofReal (δ ^ (-η) * n) * volume U) →
  ENNReal.ofReal (A * δ ^ e) * volume (prism a b c e₁ e₂ e₃) ≤
    volume (prism a b c e₁ e₂ e₃ ∩ Metric.thickening a (⋃ i, Y i))

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
