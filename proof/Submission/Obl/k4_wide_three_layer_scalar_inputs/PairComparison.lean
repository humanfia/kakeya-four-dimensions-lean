import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inputs
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.PairCompare

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory
open Inherited.Native Inherited.MatchGML2D Inherited.Core

/-- The precise two-family comparison supplied by the matching premise.
This names the existing comparison theorem, with no new analytic input. -/
def PairComparison (α : Type) [MeasurableSpace α] (d η R₀ : ℝ) : Prop :=
  ∀ (ρs : Measure (α × ℝ)) [IsFiniteMeasure ρs] (yf : α → ℝ), Measurable yf →
      ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
        (C₁ : ι₁ → Set α) (C₂ : ι₂ → Set α)
        (F₁ : ι₁ → Fin 6 → ℝ) (F₂ : ι₂ → Fin 6 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
        (δ Mst A B w : ℝ),
        (∀ i, MeasurableSet (C₁ i)) → (∀ j, MeasurableSet (C₂ j)) →
        (∀ j j', j ≠ j' → Disjoint (C₂ j) (C₂ j')) →
        (∀ i i', i ≠ i' → Disjoint (C₁ i) (C₁ i')) →
        0 < δ → R₀ * δ ≤ Mst → 1 ≤ A → A ≤ (Mst / δ) ^ η →
        0 < w → w ≤ 1 / 4 → 18 * B * w ≤ δ →
        (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
        (∀ i k, |F₁ i k| ≤ B) → (∀ j k, |F₂ j k| ≤ B) →
        (∀ i (x : ℝ), ρs ((C₁ i ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₁ i * w)) →
        (∀ j (x : ℝ), ρs ((C₂ j ∩ {l | yf l ∈ Icc (x - w) x}) ×ˢ univ) ≤
          ENNReal.ofReal (A * T₂ j * w)) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ d) →
        (∀ (r : Fin 6 → ℝ) (M : ℝ), Mst ≤ M →
          ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤
            A * (M / δ) ^ d) →
        (∀ i j, ∀ᵐ p ∂ρs, p.1 ∈ C₁ i → p.1 ∈ C₂ j → yf p.1 ∈ closeSet (F₁ i) (F₂ j) δ) →
        (∑ i, ∑ j ∈ Finset.univ.filter (fun j => ∃ k, Mst ≤ |F₁ i k - F₂ j k|),
            ρs ((C₁ i ∩ C₂ j) ×ˢ univ)) ≤
          ENNReal.ofReal (A * (Mst / δ) ^ (-η) * (∑ i, T₁ i + ∑ j, T₂ j))

theorem match_comparison_constants {α : Type} [MeasurableSpace α]
    (hM : Match) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ PairComparison α d η R₀ := by
  exact pair_compare (α := α) hM hd0 hd1

end Submission.Obl.k4_wide_three_layer_scalar_inputs
