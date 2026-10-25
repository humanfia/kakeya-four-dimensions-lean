/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PosteriorRows.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.PosteriorFinalCaps

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

noncomputable section

def activeFineBins {X J : Type*} [MeasurableSpace X] [DecidableEq J]
    (μ : Measure X) (A : Set X) (code : X → J) (F : Finset J) : Finset J := by
  classical
  exact F.filter (fun j => μ {p | p ∈ A ∧ code p = j} ≠ 0)

/-- A positive entry with a relative fine-palette ceiling must see the
corresponding amount of original palette weight. No conditional
independence is used. -/
theorem posterior_row_palette_floor {X J : Type*} [MeasurableSpace X] [DecidableEq J]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : μ A ≠ 0)
    (code : X → J) (F : Finset J) (hcover : ∀ p ∈ A, code p ∈ F)
    (weight : J → ℝ≥0∞) (C P : ℝ≥0∞) (hP₀ : P ≠ 0) (hPt : P ≠ ∞)
    (hcap : ∀ j ∈ F, μ {p | p ∈ A ∧ code p = j} ≤ ((C * weight j) / P) * μ A) :
    P ≤ C * ∑ j ∈ activeFineBins μ A code F, weight j := by
  classical
  let G := activeFineBins μ A code F
  have hG : G ⊆ F := Finset.filter_subset _ _
  have hsum : (∑ j ∈ G, μ {p | p ∈ A ∧ code p = j}) =
      ∑ j ∈ F, μ {p | p ∈ A ∧ code p = j} := by
    apply Finset.sum_subset hG
    intro j hjF hjG
    by_contra hn
    exact hjG (Finset.mem_filter.mpr ⟨hjF, hn⟩)
  have hmass : μ A ≤ ((C * ∑ j ∈ G, weight j) / P) * μ A := by
    calc
      μ A ≤ μ (⋃ j ∈ F, {p | p ∈ A ∧ code p = j}) :=
        measure_mono (fun p hp => mem_biUnion (hcover p hp) ⟨hp, rfl⟩)
      _ ≤ ∑ j ∈ F, μ {p | p ∈ A ∧ code p = j} := measure_biUnion_finset_le F _
      _ = ∑ j ∈ G, μ {p | p ∈ A ∧ code p = j} := hsum.symm
      _ ≤ ∑ j ∈ G, ((C * weight j) / P) * μ A := Finset.sum_le_sum
        (fun j hj => hcap j (hG hj))
      _ = _ := by simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  have hratio : 1 ≤ (C * ∑ j ∈ G, weight j) / P :=
    (ENNReal.mul_le_mul_iff_left hA (measure_ne_top μ A)).mp
      (by simpa only [one_mul] using hmass)
  have hscaled := mul_le_mul_of_nonneg_right hratio (show (0 : ℝ≥0∞) ≤ P from zero_le)
  simpa only [one_mul, ENNReal.div_mul_cancel hP₀ hPt] using hscaled

theorem posterior_row_palette_floor_real {X J : Type*} [MeasurableSpace X] [DecidableEq J]
    (μ : Measure X) [IsFiniteMeasure μ] (A : Set X) (hA : μ A ≠ 0)
    (code : X → J) (F : Finset J) (hcover : ∀ p ∈ A, code p ∈ F)
    (weight : J → ℝ≥0∞) (C P : ℝ≥0∞) (hCt : C ≠ ∞) (hP₀ : P ≠ 0) (hPt : P ≠ ∞)
    (hweight : ∀ j ∈ F, weight j ≠ ∞)
    (hcap : ∀ j ∈ F, μ {p | p ∈ A ∧ code p = j} ≤ ((C * weight j) / P) * μ A) :
    P.toReal ≤ C.toReal * ∑ j ∈ activeFineBins μ A code F, (weight j).toReal := by
  have hfin (j : J) (hj : j ∈ activeFineBins μ A code F) : weight j ≠ ∞ :=
    hweight j (Finset.mem_filter.mp hj).1
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hCt (ENNReal.sum_ne_top.mpr hfin))
    (posterior_row_palette_floor μ A hA code F hcover weight C P hP₀ hPt hcap)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_sum hfin] using h

end

end Submission.Obl.k4_scalar_graph_residual_discovery
