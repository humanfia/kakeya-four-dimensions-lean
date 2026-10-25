/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/BlockSelection.lean`. Original attributions are retained below. -/
import Mathlib

/-! Select one genuine native entry per endpoint/time block from its short list.
Only an inverse-list-size mass loss is paid, in the original current law. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal

noncomputable section

def optionalEvent {ι Ω : Type*} (E : ι → Set Ω) : Option ι → Set Ω
  | none => ∅
  | some i => E i

theorem exists_finite_cover_choice {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (E : ι → Set Ω) (F : Finset ι)
    (hcover : ∀ᵐ p ∂μ, p ∈ S → ∃ i ∈ F, p ∈ E i) :
    ∃ q : Option ι, (∀ i, q = some i → i ∈ F) ∧
      μ S ≤ (F.card : ℝ≥0∞) * μ (S ∩ optionalEvent E q) := by
  classical
  rcases F.eq_empty_or_nonempty with hF | hF
  · refine ⟨none, (by simp), ?_⟩
    have hnull : μ S = 0 := by
      apply le_antisymm _ zero_le
      have hm : S ≤ᵐ[μ] (∅ : Set Ω) := by
        filter_upwards [hcover] with p hp hpS
        simpa only [hF, Finset.notMem_empty, false_and, exists_false] using hp hpS
      simpa only [measure_empty] using measure_mono_ae hm
    rw [hnull]
    exact zero_le
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image F (fun i => μ (S ∩ E i)) hF
    refine ⟨some i, (fun j hj => by cases Option.some.inj hj; exact hi), ?_⟩
    calc
      μ S ≤ μ (⋃ j ∈ F, S ∩ E j) := by
        apply measure_mono_ae
        filter_upwards [hcover] with p hp hpS
        obtain ⟨j, hj, hpj⟩ := hp hpS
        exact mem_iUnion₂.mpr ⟨j, hj, hpS, hpj⟩
      _ ≤ ∑ j ∈ F, μ (S ∩ E j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ F, μ (S ∩ E i) := Finset.sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp [optionalEvent, nsmul_eq_mul]

/-- Fix all block representatives at once, retaining mass in the same original
measure. Closed-block overlaps may be null rather than literally empty. -/
theorem exists_block_list_selection {Ω G ι : Type*} [MeasurableSpace Ω] [Fintype G]
    (μ : Measure Ω) (S : G → Set Ω) (E : G → ι → Set Ω) (F : G → Finset ι)
    {K : ℝ} (hK : 0 ≤ K)
    (hS : ∀ g, MeasurableSet (S g)) (hE : ∀ g i, MeasurableSet (E g i))
    (hdisj : Pairwise (fun g g' => AEDisjoint μ (S g) (S g')))
    (htotal : ∀ᵐ p ∂μ, ∃ g, p ∈ S g)
    (hcover : ∀ g, ∀ᵐ p ∂μ, p ∈ S g → ∃ i ∈ F g, p ∈ E g i)
    (hcard : ∀ g, ((F g).card : ℝ) ≤ K) :
    ∃ choice : G → Option ι,
      (∀ g i, choice g = some i → i ∈ F g) ∧
      MeasurableSet (⋃ g, S g ∩ optionalEvent (E g) (choice g)) ∧
      μ univ ≤ ENNReal.ofReal K * μ (⋃ g, S g ∩ optionalEvent (E g) (choice g)) := by
  classical
  choose choice hchoice hmass using fun g => exists_finite_cover_choice μ (S g) (E g) (F g) (hcover g)
  let B := fun g => S g ∩ optionalEvent (E g) (choice g)
  have hBm (g : G) : MeasurableSet (B g) := by
    cases h : choice g with
    | none => simp [B, h, optionalEvent]
    | some i => simpa only [B, h, optionalEvent] using (hS g).inter (hE g i)
  have hBd : Pairwise (fun g g' => AEDisjoint μ (B g) (B g')) := by
    intro g g' hne
    exact (hdisj hne).mono inter_subset_left inter_subset_left
  refine ⟨choice, hchoice, MeasurableSet.iUnion hBm, ?_⟩
  calc
    μ univ ≤ μ (⋃ g, S g) := by
      apply measure_mono_ae
      filter_upwards [htotal] with p hp _
      exact mem_iUnion.mpr hp
    _ ≤ ∑ g, μ (S g) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ g, ENNReal.ofReal K * μ (B g) := by
      apply Finset.sum_le_sum
      intro g _
      exact (hmass g).trans (mul_le_mul' (by exact_mod_cast ENNReal.ofReal_le_ofReal (hcard g)) le_rfl)
    _ = ENNReal.ofReal K * μ (⋃ g, B g) := by
      have hsum : μ (⋃ g, B g) = ∑ g, μ (B g) := by
        simpa using (measure_biUnion_finset₀ (s := Finset.univ) (f := B)
          (fun g _ g' _ hgg => hBd hgg) (fun g _ => (hBm g).nullMeasurableSet))
      rw [← Finset.mul_sum, hsum]

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
