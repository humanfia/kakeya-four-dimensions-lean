/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalPaletteCount.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualPosteriorCount
import Submission.Obl.k4_scalar_graph_residual_discovery.VelocityBoundaries
import Submission.Obl.k4_scalar_grid_parameter_preparation.VelocityBins

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

def velocityMeetingBins (ρ β : ℝ) (c : ℤ) : Finset ℤ :=
  Finset.Icc ⌊(c : ℝ) * ρ / β⌋ ⌊((c : ℝ) + 1) * ρ / β⌋

theorem mem_velocityMeetingBins {ρ β v : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    {c : ℤ} (hc : (⌊v / ρ⌋ : ℤ) = c) : ⌊v / β⌋ ∈ velocityMeetingBins ρ β c := by
  have hh := Int.floor_eq_iff.mp hc
  have hlo := (le_div_iff₀ hρ).mp hh.1
  have hhi := ((div_lt_iff₀ hρ).mp hh.2).le
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (div_le_div_of_nonneg_right hlo hβ.le),
      Int.floor_mono (div_le_div_of_nonneg_right hhi hβ.le)⟩

/-- Only contained original fine bins enter the coarse palette sum.
Endpoint bins will be charged by their column count instead. -/
theorem contained_velocity_palette_sum_le (π : Measure ℝ) [IsFiniteMeasure π]
    (ρ β : ℝ) (c : ℤ) (J : Finset ℤ)
    (hsub : ∀ j ∈ J, scalarVelocityBin β j ⊆ scalarVelocityBin ρ c) :
    ∑ j ∈ J, (π (scalarVelocityBin β j)).toReal ≤ (π (scalarVelocityBin ρ c)).toReal := by
  have hdisj : (↑J : Set ℤ).PairwiseDisjoint (scalarVelocityBin β) := by
    intro i _ j _ hij
    exact scalarVelocityBin_disjoint β hij
  have hm : (∑ j ∈ J, π (scalarVelocityBin β j)) ≤ π (scalarVelocityBin ρ c) := by
    rw [← measure_biUnion_finset hdisj (fun j _ => measurableSet_scalarVelocityBin β j)]
    apply measure_mono
    intro v hv
    obtain ⟨j, hjJ, hv⟩ := mem_iUnion₂.mp hv
    exact hsub j hjJ hv
  have hh := ENNReal.toReal_mono (measure_ne_top π _) hm
  rw [ENNReal.toReal_sum (fun j _ => measure_ne_top π _)] at hh
  exact hh

/-- Concrete original velocity bins instantiate the posterior list
count: the full coarse palette cancels, while its at most two crossing
fine bins are charged separately. No nested-grid assumption is used. -/
theorem original_palette_entry_count {X A : Type*}
    [MeasurableSpace X] [DecidableEq A]
    (μ : Measure X) [IsFiniteMeasure μ] (π : Measure ℝ) [IsFiniteMeasure π]
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (c : ℤ) (v : X → ℝ)
    (states : Finset A) (entry : A → Set X)
    (compatible : A → ℤ → Prop) [DecidableRel compatible]
    (hcompatible : ∀ a j, compatible a j ↔ μ {p | p ∈ entry a ∧ (⌊v p / β⌋ : ℤ) = j} ≠ 0)
    (hpositive : ∀ a ∈ states, μ (entry a) ≠ 0)
    (hcoarse : ∀ a ∈ states, ∀ p ∈ entry a, (⌊v p / ρ⌋ : ℤ) = c)
    (C η : ℝ≥0∞) (hCt : C ≠ ∞) (hη₀ : η ≠ 0) (hηt : η ≠ ∞)
    (hP₀ : π (scalarVelocityBin ρ c) ≠ 0)
    (hcap : ∀ a ∈ states, ∀ j,
      μ {p | p ∈ entry a ∧ (⌊v p / β⌋ : ℤ) = j} ≤
        ((C * π (scalarVelocityBin β j)) / (η * π (scalarVelocityBin ρ c))) * μ (entry a))
    {K : ℝ} (hK : 0 ≤ K)
    (hcolumn : ∀ j, ((Finset.bipartiteBelow compatible states j).card : ℝ) ≤ K) :
    (states.card : ℝ) ≤ (C.toReal / η.toReal + 2) * K := by
  classical
  let bins := velocityMeetingBins ρ β c
  let interior := bins.filter (fun j => scalarVelocityBin β j ⊆ scalarVelocityBin ρ c)
  let boundary := velocityBoundaryBins ρ β c
  have hcover (a : A) (ha : a ∈ states) (p : X) (hp : p ∈ entry a) : ⌊v p / β⌋ ∈ bins :=
    mem_velocityMeetingBins hρ hβ (hcoarse a ha p hp)
  have hclassification (a : A) (ha : a ∈ states) (j : ℤ) (hj : j ∈ bins)
      (haj : compatible a j) : j ∈ interior ∨ j ∈ boundary := by
    obtain ⟨p, hp, hpj⟩ := nonempty_of_measure_ne_zero ((hcompatible a j).mp haj)
    rcases fine_velocity_bin_subset_or_boundary hρ hβ c j ⟨v p, hcoarse a ha p hp, hpj⟩ with hb | hi
    · exact Or.inr hb
    · exact Or.inl (Finset.mem_filter.mpr ⟨hj, hi⟩)
  have hmass : (∑ j ∈ interior, (π (scalarVelocityBin β j)).toReal) ≤
      (π (scalarVelocityBin ρ c)).toReal :=
    contained_velocity_palette_sum_le π ρ β c interior (fun j hj => (Finset.mem_filter.mp hj).2)
  have hh := residual_list_count_of_posterior_caps μ states entry (fun p => ⌊v p / β⌋)
    bins interior boundary compatible hcompatible hpositive hcover hclassification
    (fun j => π (scalarVelocityBin β j)) C η (π (scalarVelocityBin ρ c)) hCt hη₀ hηt hP₀
    (measure_ne_top π _) (fun j _ => measure_ne_top π _) hmass
    (fun a ha j _ => hcap a ha j) hK (fun j _ => hcolumn j) (fun j _ => hcolumn j)
  have hb : (boundary.card : ℝ) ≤ 2 := by exact_mod_cast card_velocityBoundaryBins_le_two ρ β c
  exact hh.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl hb) hK)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
