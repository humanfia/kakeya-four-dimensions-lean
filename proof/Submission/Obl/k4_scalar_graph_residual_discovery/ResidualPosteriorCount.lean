/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ResidualPosteriorCount.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PosteriorRows
import Submission.Obl.k4_scalar_graph_residual_discovery.BoundaryPaletteLists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

/-- The original-palette posterior ceilings and fine-bin column lists give
a residual list bound. Endpoint bins are charged separately, so only
fully contained bins enter the coarse palette sum. -/
theorem residual_list_count_of_posterior_caps {X A J : Type*}
    [MeasurableSpace X] [DecidableEq A] [DecidableEq J]
    (μ : Measure X) [IsFiniteMeasure μ] (states : Finset A)
    (entry : A → Set X) (code : X → J) (bins interior boundary : Finset J)
    (compatible : A → J → Prop) [DecidableRel compatible]
    (hcompatible : ∀ a j, compatible a j ↔ μ {p | p ∈ entry a ∧ code p = j} ≠ 0)
    (hpositive : ∀ a ∈ states, μ (entry a) ≠ 0)
    (hcover : ∀ a ∈ states, ∀ p ∈ entry a, code p ∈ bins)
    (hclassification : ∀ a ∈ states, ∀ j ∈ bins, compatible a j → j ∈ interior ∨ j ∈ boundary)
    (weight : J → ℝ≥0∞) (C η P : ℝ≥0∞)
    (hCt : C ≠ ∞) (hη₀ : η ≠ 0) (hηt : η ≠ ∞) (hP₀ : P ≠ 0) (hPt : P ≠ ∞)
    (hweight : ∀ j ∈ bins, weight j ≠ ∞)
    (hmass : ∑ j ∈ interior, (weight j).toReal ≤ P.toReal)
    (hcap : ∀ a ∈ states, ∀ j ∈ bins,
      μ {p | p ∈ entry a ∧ code p = j} ≤ ((C * weight j) / (η * P)) * μ (entry a))
    {K : ℝ} (hK : 0 ≤ K)
    (hcolumn : ∀ j ∈ interior,
      ((Finset.bipartiteBelow compatible states j).card : ℝ) ≤ K)
    (hboundary : ∀ j ∈ boundary,
      ((Finset.bipartiteBelow compatible states j).card : ℝ) ≤ K) :
    (states.card : ℝ) ≤ (C.toReal / η.toReal + (boundary.card : ℝ)) * K := by
  classical
  have hη : 0 < η.toReal := ENNReal.toReal_pos hη₀ hηt
  apply palette_weighted_list_count_with_boundary states interior boundary
    (fun j => (weight j).toReal) compatible (ENNReal.toReal_pos hP₀ hPt)
    (by positivity) hK (fun _ _ => ENNReal.toReal_nonneg) hmass ?_ hcolumn hboundary
  intro a ha hfree
  have hrow := posterior_row_palette_floor_real μ (entry a) (hpositive a ha)
    code bins (hcover a ha) weight C (η * P) hCt
    (mul_ne_zero hη₀ hP₀) (ENNReal.mul_ne_top hηt hPt) hweight (hcap a ha)
  rw [ENNReal.toReal_mul] at hrow
  have hsub : activeFineBins μ (entry a) code bins ⊆
      Finset.bipartiteAbove compatible interior a := by
    intro j hj
    obtain ⟨hjbin, hjpositive⟩ := Finset.mem_filter.mp hj
    have hjcompat := (hcompatible a j).mpr hjpositive
    have hjinterior : j ∈ interior := (hclassification a ha j hjbin hjcompat).resolve_right
      (fun hjboundary => hfree j hjboundary hjcompat)
    exact (Finset.mem_bipartiteAbove compatible).mpr ⟨hjinterior, hjcompat⟩
  have hsum : (∑ j ∈ activeFineBins μ (entry a) code bins, (weight j).toReal) ≤
      ∑ j ∈ Finset.bipartiteAbove compatible interior a, (weight j).toReal :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => ENNReal.toReal_nonneg)
  have hscaled := hrow.trans (mul_le_mul_of_nonneg_left hsum ENNReal.toReal_nonneg)
  calc
    P.toReal ≤ (C.toReal * ∑ j ∈ Finset.bipartiteAbove compatible interior a,
        (weight j).toReal) / η.toReal := (le_div_iff₀ hη).mpr (by nlinarith only [hscaled])
    _ = _ := by ring

end Submission.Obl.k4_scalar_graph_residual_discovery
