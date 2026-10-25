-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.RegularPruning.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open scoped Classical

open MeasureTheory Set
open scoped ENNReal

/-- Integrating a finite overlap bound controls the sum of the masses of the
cells cut out of a measurable reference set. -/
theorem sum_measure_inter_le_of_overlap {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (C : ι → Set α)
    (hC : ∀ i ∈ S, MeasurableSet (C i)) (W : Set α) (hW : MeasurableSet W)
    (M : ℕ) (hM : ∀ p ∈ W, (S.filter fun i => p ∈ C i).card ≤ M) :
    ∑ i ∈ S, μ (W ∩ C i) ≤ M * μ W := by
  classical
  calc
    ∑ i ∈ S, μ (W ∩ C i) = ∫⁻ p, ∑ i ∈ S, (W ∩ C i).indicator (fun _ => (1 : ℝ≥0∞)) p ∂μ := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [lintegral_indicator_const (hW.inter (hC i hi)), one_mul]
      · intro i hi
        exact measurable_const.indicator (hW.inter (hC i hi))
    _ ≤ ∫⁻ p, W.indicator (fun _ => (M : ℝ≥0∞)) p ∂μ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ W
      · simp only [indicator_of_mem hp]
        have heq : (∑ i ∈ S, (W ∩ C i).indicator (fun _ => (1 : ℝ≥0∞)) p) =
            ((S.filter fun i => p ∈ C i).card : ℝ≥0∞) := by
          simp [Set.indicator, hp, Finset.sum_boole]
        rw [heq]
        exact_mod_cast hM p hp
      · simp [Set.indicator, hp]
    _ = M * μ W := lintegral_indicator_const hW _

/-- Delete sparse cells until each surviving cell has the prescribed mass.
Each cell is charged at most once, even when the cells overlap. -/
theorem regular_subshading_finite {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (C : ι → Set α) (t : ι → ℝ≥0∞)
    (hC : ∀ i ∈ S, MeasurableSet (C i)) (Y : Set α) (hY : MeasurableSet Y) :
    ∃ Z : Set α, MeasurableSet Z ∧ Z ⊆ Y ∧
      μ Y ≤ μ Z + ∑ i ∈ S, t i ∧
      ∀ i ∈ S, Z ∩ C i = ∅ ∨ t i < μ (Z ∩ C i) := by
  classical
  induction S using Finset.strongInductionOn generalizing Y with
  | _ S ih =>
    by_cases hgood : ∀ i ∈ S, Y ∩ C i = ∅ ∨ t i < μ (Y ∩ C i)
    · exact ⟨Y, hY, Subset.rfl, le_add_right le_rfl, hgood⟩
    · push Not at hgood
      obtain ⟨i, hiS, hne, hi⟩ := hgood
      obtain ⟨Z, hZ, hZY, hmass, hregular⟩ := ih (S.erase i) (Finset.erase_ssubset hiS)
        (fun j hj => hC j (Finset.mem_of_mem_erase hj)) (Y \ C i) (hY.diff (hC i hiS))
      refine ⟨Z, hZ, hZY.trans sdiff_subset, ?_, ?_⟩
      · have hsplit : μ Y ≤ μ (Y \ C i) + μ (Y ∩ C i) := by
          calc
            μ Y = μ ((Y \ C i) ∪ (Y ∩ C i)) := by rw [sdiff_union_inter]
            _ ≤ _ := measure_union_le _ _
        calc
          μ Y ≤ μ (Y \ C i) + μ (Y ∩ C i) := hsplit
          _ ≤ (μ Z + ∑ j ∈ S.erase i, t j) + t i := add_le_add hmass hi
          _ = μ Z + ∑ j ∈ S, t j := by
            rw [add_assoc, Finset.sum_erase_add _ _ hiS]
      · intro j hj
        by_cases hji : j = i
        · left
          subst j
          apply eq_empty_iff_forall_notMem.mpr
          intro p hp
          exact (hZY hp.1).2 hp.2
        · exact hregular j (Finset.mem_erase.mpr ⟨hji, hj⟩)

/-- In particular, a family of sparse-cell budgets totaling at most half the
initial mass leaves a measurable subshading with at least half that mass. -/
theorem regular_subshading_half {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (C : ι → Set α) (t : ι → ℝ≥0∞)
    (hC : ∀ i ∈ S, MeasurableSet (C i)) (Y : Set α) (hY : MeasurableSet Y)
    (hfin : μ Y ≠ ⊤) (hbudget : ∑ i ∈ S, t i ≤ (1 / 2 : ℝ≥0∞) * μ Y) :
    ∃ Z : Set α, MeasurableSet Z ∧ Z ⊆ Y ∧
      (1 / 2 : ℝ≥0∞) * μ Y ≤ μ Z ∧
      ∀ i ∈ S, Z ∩ C i = ∅ ∨ t i < μ (Z ∩ C i) := by
  obtain ⟨Z, hZ, hsub, hmass, hreg⟩ := regular_subshading_finite μ S C t hC Y hY
  refine ⟨Z, hZ, hsub, ?_, hreg⟩
  have hhalf : (1 / 2 : ℝ≥0∞) * μ Y + (1 / 2 : ℝ≥0∞) * μ Y = μ Y := by
    rw [← add_mul, one_div, ENNReal.inv_two_add_inv_two, one_mul]
  have hh : (1 / 2 : ℝ≥0∞) * μ Y + (1 / 2 : ℝ≥0∞) * μ Y ≤
      μ Z + (1 / 2 : ℝ≥0∞) * μ Y := by
    rw [hhalf]
    exact hmass.trans (add_le_add_right hbudget _)
  exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hfin)).mp hh

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
