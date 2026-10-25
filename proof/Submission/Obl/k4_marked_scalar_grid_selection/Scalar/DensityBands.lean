/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/DensityBands.lean. -/
import Mathlib

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

local instance densityBandsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance densityBandsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- The mass of a record in the original weighted atom table. -/
noncomputable def recordMass {ι κ : Type*} (I : Finset ι) (w : ι → ℝ≥0∞)
    (code : ι → κ) (c : κ) : ℝ≥0∞ := by
  classical
  exact ∑ a ∈ I.filter (fun a => code a = c), w a

/-- Distinct retained records charge disjoint fibers of the original table. -/
theorem recordMass_sum_le {ι κ : Type*} (I T : Finset ι) (hT : T ⊆ I)
    (w : ι → ℝ≥0∞) (code : ι → κ) :
    ∑ c ∈ T.image code, recordMass I w code c ≤ ∑ a ∈ I, w a := by
  classical
  calc
    _ ≤ ∑ c ∈ I.image code, recordMass I w code c := by
      exact Finset.sum_le_sum_of_subset (Finset.image_subset_image hT)
    _ = _ := by
      exact Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) _

/-- A band for the old record masses gives a band for the exact mixture density.
The two geometric inputs are support volume and overlap of the record supports.
No part of an atom is selected. -/
theorem atom_density_band {ι κ Y : Type*} [MeasurableSpace Y]
    (ρ : Measure Y) (I T : Finset ι) (hT : T ⊆ I)
    (w : ι → ℝ≥0∞) (code : ι → κ) (S : κ → Set Y)
    (f : ι → Y → ℝ≥0∞) (hf : ∀ a, Measurable (f a))
    (hS : ∀ c, MeasurableSet (S c)) (A D lower upper ε : ℝ≥0∞)
    (hvol : ∀ c ∈ T.image code, ρ (S c) ≤ A)
    (hoverlap : ∀ y, ((T.image code).filter (fun c => y ∈ S c)).card ≤ D)
    (hkernel : ∀ a ∈ T, ∀ y, f a y ≤ (S (code a)).indicator (fun _ => w a) y)
    (hlower : ∀ c ∈ T.image code, lower ≤ recordMass I w code c)
    (hupper : ∀ c ∈ T.image code, recordMass I w code c ≤ upper) :
    let F : Y → ℝ≥0∞ := fun y => ∑ a ∈ T, f a y
    (ρ.withDensity F) {y | F y < ε * lower ∨ D * upper < F y} ≤
      ε * A * ∑ a ∈ I, w a := by
  classical
  intro F
  let C := T.image code
  let R : Set Y := ⋃ c ∈ C, S c
  have hR : MeasurableSet R := by
    exact Finset.measurableSet_biUnion _ (fun c _ => hS c)
  have hF : Measurable F := by fun_prop
  have hfzero (a : ι) (ha : a ∈ T) (y : Y) (hy : y ∉ S (code a)) : f a y = 0 := by
    apply le_antisymm _ zero_le
    simpa only [Set.indicator_of_notMem hy] using hkernel a ha y
  have hzero (y : Y) (hy : y ∉ R) : F y = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply hfzero a ha
    intro hy'
    exact hy (mem_iUnion₂.mpr ⟨code a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hy'⟩)
  have hpoint (y : Y) : F y ≤ D * upper := by
    have hgroup : F y = ∑ c ∈ C, ∑ a ∈ T.filter (fun a => code a = c), f a y := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) _
    rw [hgroup]
    calc
      _ ≤ ∑ c ∈ C, (S c).indicator (fun _ => recordMass I w code c) y := by
        apply Finset.sum_le_sum
        intro c hc
        by_cases hy : y ∈ S c
        · rw [Set.indicator_of_mem hy]
          calc
            _ ≤ ∑ a ∈ T.filter (fun a => code a = c), w a := by
              apply Finset.sum_le_sum
              intro a ha
              obtain ⟨haT, hac⟩ := Finset.mem_filter.mp ha
              simpa only [hac, Set.indicator_of_mem hy] using hkernel a haT y
            _ ≤ recordMass I w code c := by
              apply Finset.sum_le_sum_of_subset
              intro a ha
              obtain ⟨haT, hac⟩ := Finset.mem_filter.mp ha
              exact Finset.mem_filter.mpr ⟨hT haT, hac⟩
        · rw [Set.indicator_of_notMem hy]
          exact le_of_eq (Finset.sum_eq_zero fun a ha =>
            hfzero a (Finset.mem_filter.mp ha).1 y (by
              simpa only [(Finset.mem_filter.mp ha).2] using hy))
      _ ≤ ∑ c ∈ C, (S c).indicator (fun _ => upper) y := by
        apply Finset.sum_le_sum
        intro c hc
        exact Set.indicator_le_indicator (hupper c hc)
      _ = (((C.filter (fun c => y ∈ S c)).card : ℕ) : ℝ≥0∞) * upper := by
        simp only [Set.indicator_apply]
        rw [← Finset.sum_filter]
        simp
      _ ≤ D * upper := mul_le_mul' (hoverlap y) le_rfl
  have hbudget : ((C.card : ℕ) : ℝ≥0∞) * lower ≤ ∑ a ∈ I, w a := by
    calc
      _ = ∑ _c ∈ C, lower := by simp
      _ ≤ ∑ c ∈ C, recordMass I w code c :=
        Finset.sum_le_sum fun c hc => hlower c hc
      _ ≤ _ := recordMass_sum_le I T hT w code
  have hvolume : ρ R ≤ (C.card : ℝ≥0∞) * A := by
    calc
      _ ≤ ∑ c ∈ C, ρ (S c) := measure_biUnion_finset_le C (fun c => S c)
      _ ≤ ∑ _c ∈ C, A := Finset.sum_le_sum fun c hc => hvol c hc
      _ = _ := by simp
  have hbad : MeasurableSet {y | F y < ε * lower ∨ D * upper < F y} := by
    exact (measurableSet_lt hF measurable_const).union (measurableSet_lt measurable_const hF)
  rw [withDensity_apply _ hbad, ← lintegral_indicator hbad]
  calc
    _ ≤ ∫⁻ y, R.indicator (fun _ => ε * lower) y ∂ρ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ R
      · rw [Set.indicator_of_mem hy]
        by_cases hb : F y < ε * lower ∨ D * upper < F y
        · simp only [Set.indicator_apply, mem_ofPred_eq, ite_eq_left hb]
          exact hb.resolve_right (not_lt_of_ge (hpoint y)) |>.le
        · simp only [Set.indicator_apply, mem_ofPred_eq, ite_eq_right hb]
          exact zero_le
      · rw [Set.indicator_of_notMem hy]
        simp only [Set.indicator_apply, hzero y hy, ite_self]
        exact le_rfl
    _ = ε * lower * ρ R := lintegral_indicator_const hR _
    _ ≤ ε * lower * ((C.card : ℝ≥0∞) * A) := mul_le_mul' le_rfl hvolume
    _ = ε * A * ((C.card : ℝ≥0∞) * lower) := by ring
    _ ≤ _ := mul_le_mul' le_rfl hbudget

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
