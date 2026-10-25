/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PosteriorPointLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalPaletteCount

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

/-- Current floors make every observed original entry positive. Choose
one such entry for each observed residual label, then use the original
palette posterior ceilings and per-fine-bin column lists to bound the
POINTWISE list. Labels of null original entries cannot appear. -/
theorem pointwise_labels_of_original_posterior_entries {X A : Type*}
    [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (π : Measure ℝ) [IsFiniteMeasure π]
    (E : Set X) (record : X → A) (label : A → ℤ)
    (hfinite : (record '' E).Finite) (entry : A → Set X)
    (hpositive : ∀ a ∈ record '' E, μ (entry a) ≠ 0)
    {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (c : ℤ) (v : X → ℝ)
    (hcoarse : ∀ a ∈ record '' E, ∀ p ∈ entry a, (⌊v p / ρ⌋ : ℤ) = c)
    (C η : ℝ≥0∞) (hCt : C ≠ ∞) (hη₀ : η ≠ 0) (hηt : η ≠ ∞)
    (hP₀ : π (scalarVelocityBin ρ c) ≠ 0)
    (hcap : ∀ a ∈ record '' E, ∀ j,
      μ {p | p ∈ entry a ∧ (⌊v p / β⌋ : ℤ) = j} ≤
        ((C * π (scalarVelocityBin β j)) / (η * π (scalarVelocityBin ρ c))) * μ (entry a))
    {K : ℝ} (hK : 0 ≤ K)
    (hcolumns : ∀ j, ∃ L : Finset ℤ, (L.card : ℝ) ≤ K ∧
      ∀ a ∈ record '' E,
        μ {p | p ∈ entry a ∧ (⌊v p / β⌋ : ℤ) = j} ≠ 0 → label a ∈ L) :
    ∃ L : Finset ℤ, (L.card : ℝ) ≤ (C.toReal / η.toReal + 2) * K ∧
      ∀ p ∈ E, label (record p) ∈ L := by
  classical
  let L := (hfinite.image label).toFinset
  have hwitness (z : L) : ∃ a ∈ record '' E, label a = z.1 :=
    (hfinite.image label).mem_toFinset.mp z.2
  let a (z : L) : A := Classical.choose (hwitness z)
  have hobs (z : L) : a z ∈ record '' E := (Classical.choose_spec (hwitness z)).1
  have hlabel (z : L) : label (a z) = z.1 := (Classical.choose_spec (hwitness z)).2
  let entries (z : L) := entry (a z)
  let compatible (z : L) (j : ℤ) : Prop :=
    μ {p | p ∈ entries z ∧ (⌊v p / β⌋ : ℤ) = j} ≠ 0
  have hcolumn (j : ℤ) :
      ((Finset.bipartiteBelow compatible (Finset.univ : Finset L) j).card : ℝ) ≤ K := by
    obtain ⟨Q, hQcard, hQ⟩ := hcolumns j
    let neighbors := Finset.bipartiteBelow compatible (Finset.univ : Finset L) j
    have hsub : neighbors.image (Subtype.val : L → ℤ) ⊆ Q := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hh := hQ (a u) (hobs u) ((Finset.mem_bipartiteBelow compatible).mp hu).2
      simpa only [hlabel] using hh
    have hcard : neighbors.card ≤ Q.card := by
      rw [← Finset.card_image_of_injective neighbors (Subtype.val_injective :
        Function.Injective (Subtype.val : L → ℤ))]
      exact Finset.card_le_card hsub
    exact (show (neighbors.card : ℝ) ≤ Q.card from by exact_mod_cast hcard).trans hQcard
  have hcount := original_palette_entry_count μ π hρ hβ c v
    (Finset.univ : Finset L) entries compatible (fun _ _ => Iff.rfl)
    (fun z _ => hpositive (a z) (hobs z))
    (fun z _ => hcoarse (a z) (hobs z)) C η hCt hη₀ hηt hP₀
    (fun z _ => hcap (a z) (hobs z)) hK hcolumn
  refine ⟨L, ?_, ?_⟩
  · simpa only [Finset.card_univ, Fintype.card_coe] using hcount
  · intro p hp
    exact (hfinite.image label).mem_toFinset.mpr ⟨record p, ⟨p, hp, rfl⟩, rfl⟩

end

end Submission.Obl.k4_scalar_graph_residual_discovery
