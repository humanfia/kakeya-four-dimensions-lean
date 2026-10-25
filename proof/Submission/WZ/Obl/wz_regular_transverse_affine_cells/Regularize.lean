-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Regularize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- Delete cells with insufficient surviving mass. A cell that has been deleted never
meets the final shading, so every deletion is charged at most once. -/
lemma finite_density_pruning {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (B : ι → Set X) (cost : ι → ℝ≥0∞) (F : Finset ι)
    (hB : ∀ i ∈ F, MeasurableSet (B i)) {Y : Set X} (hY : MeasurableSet Y) :
    ∃ H : Set X, MeasurableSet H ∧ H ⊆ Y ∧
      μ Y ≤ μ H + ∑ i ∈ F, cost i ∧
      ∀ i ∈ F, (H ∩ B i).Nonempty → cost i ≤ μ (H ∩ B i) := by
  classical
  induction F using Finset.strongInductionOn generalizing Y with
  | _ F ih =>
    by_cases hgood : ∀ i ∈ F, (Y ∩ B i).Nonempty → cost i ≤ μ (Y ∩ B i)
    · exact ⟨Y, hY, Subset.rfl, le_self_add, hgood⟩
    push Not at hgood
    obtain ⟨i, hi, hmeet, hsmall⟩ := hgood
    have hB' : ∀ j ∈ F.erase i, MeasurableSet (B j) :=
      fun j hj => hB j (Finset.mem_of_mem_erase hj)
    obtain ⟨H, hHm, hHsub, hmass, hreg⟩ :=
      ih (F.erase i) (Finset.erase_ssubset hi) hB' (hY.diff (hB i hi))
    refine ⟨H, hHm, hHsub.trans sdiff_subset, ?_, ?_⟩
    · calc μ Y = μ (Y \ B i) + μ (Y ∩ B i) := (measure_sdiff_add_inter Y (hB i hi)).symm
        _ ≤ (μ H + ∑ j ∈ F.erase i, cost j) + cost i := add_le_add hmass hsmall.le
        _ = μ H + ∑ j ∈ F, cost j := by
          rw [add_assoc, Finset.sum_erase_add _ _ hi]
    · intro j hj hmeet
      by_cases hji : j = i
      · subst j
        obtain ⟨p, hpH, hpB⟩ := hmeet
        exact False.elim ((hHsub hpH).2 hpB)
      · exact hreg j (Finset.mem_erase.mpr ⟨hji, hj⟩) hmeet

/-- A version with a common relative density threshold. -/
lemma finite_relative_density_pruning {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (P : Set X) (B : ι → Set X) (F : Finset ι) (τ : ℝ≥0∞)
    (hB : ∀ i ∈ F, MeasurableSet (B i)) {Y : Set X} (hY : MeasurableSet Y) :
    ∃ H : Set X, MeasurableSet H ∧ H ⊆ Y ∧
      μ Y ≤ μ H + τ * ∑ i ∈ F, μ (P ∩ B i) ∧
      ∀ i ∈ F, ∀ p ∈ H ∩ B i, τ * μ (P ∩ B i) ≤ μ (H ∩ B i) := by
  obtain ⟨H, hHm, hHsub, hmass, hreg⟩ :=
    finite_density_pruning μ B (fun i => τ * μ (P ∩ B i)) F hB hY
  refine ⟨H, hHm, hHsub, ?_, ?_⟩
  · simpa only [Finset.mul_sum] using hmass
  · intro i hi p hp
    exact hreg i hi ⟨p, hp⟩

/-- A finite family of measurable partitions gives a density core with loss equal to
one threshold times the number of partitions. -/
lemma partition_density_pruning {X ι κ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (μ : Measure X) (P : Set X) (hP : MeasurableSet P)
    (B : ι → κ → Set X) (hB : ∀ i j, MeasurableSet (B i j))
    (hdisj : ∀ i, Pairwise (fun j k => Disjoint (B i j) (B i k)))
    (hcover : ∀ i, P ⊆ ⋃ j, B i j)
    (τ : ℝ≥0∞) {Y : Set X} (hY : MeasurableSet Y) :
    ∃ H : Set X, MeasurableSet H ∧ H ⊆ Y ∧
      μ Y ≤ μ H + τ * Fintype.card ι * μ P ∧
      ∀ i j, ∀ p ∈ H ∩ B i j, τ * μ (P ∩ B i j) ≤ μ (H ∩ B i j) := by
  classical
  obtain ⟨H, hHm, hHsub, hmass, hreg⟩ :=
    finite_relative_density_pruning μ P (fun ij : ι × κ => B ij.1 ij.2)
      Finset.univ τ (by intro i _; exact hB i.1 i.2) hY
  have hsum (i : ι) : ∑ j, μ (P ∩ B i j) = μ P := by
    have hd : Pairwise (fun j k => Disjoint (P ∩ B i j) (P ∩ B i k)) := by
      intro j k hjk
      exact (hdisj i hjk).mono inter_subset_right inter_subset_right
    have heq : (⋃ j, P ∩ B i j) = P := by
      rw [← inter_iUnion, inter_eq_left]
      exact hcover i
    simpa only [tsum_fintype, heq] using
      (measure_iUnion (μ := μ) hd (fun j => hP.inter (hB i j))).symm
  have hsum' : ∑ ij : ι × κ, μ (P ∩ B ij.1 ij.2) = Fintype.card ι * μ P := by
    rw [Fintype.sum_prod_type]
    simp [hsum]
  refine ⟨H, hHm, hHsub, ?_, ?_⟩
  · simpa only [hsum', mul_assoc] using hmass
  · intro i j p hp
    exact hreg (i, j) (Finset.mem_univ _) p hp

/-- The budget form directly yields a retained half of the initial shading mass. -/
lemma half_mass_of_pruning_budget {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {Y H : Set X} {budget : ℝ≥0∞} (hYfin : μ Y ≠ ∞)
    (hmass : μ Y ≤ μ H + budget) (hbudget : budget ≤ (1 / 2 : ℝ≥0∞) * μ Y) :
    (1 / 2 : ℝ≥0∞) * μ Y ≤ μ H := by
  have heq : (1 / 2 : ℝ≥0∞) * μ Y + (1 / 2 : ℝ≥0∞) * μ Y = μ Y := by
    rw [← add_mul]
    norm_num [ENNReal.inv_two_add_inv_two]
  have h := hmass.trans (add_le_add le_rfl hbudget)
  nth_rw 1 [← heq] at h
  exact ENNReal.le_of_add_le_add_right
    (ENNReal.mul_ne_top (by norm_num) hYfin) h

open Classical in
/-- Uniform finite overlap bounds the sum of intersection measures for any measure. -/
lemma sum_inter_measure_le_of_overlap {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (P : Set X) (hP : MeasurableSet P) (B : ι → Set X)
    (F : Finset ι) (hB : ∀ i ∈ F, MeasurableSet (B i)) (M : ℕ)
    (hover : ∀ p ∈ P, (F.filter (fun i => p ∈ B i)).card ≤ M) :
    ∑ i ∈ F, μ (P ∩ B i) ≤ (M : ℝ≥0∞) * μ P := by
  classical
  calc ∑ i ∈ F, μ (P ∩ B i)
      = ∫⁻ p, ∑ i ∈ F, (P ∩ B i).indicator (fun _ => (1 : ℝ≥0∞)) p ∂μ := by
        rw [lintegral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [lintegral_indicator_const (hP.inter (hB i hi)), one_mul]
        · intro i hi
          exact measurable_const.indicator (hP.inter (hB i hi))
    _ ≤ ∫⁻ p, P.indicator (fun _ => (M : ℝ≥0∞)) p ∂μ := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ P
      · simp only [Set.indicator_apply, mem_inter_iff, hp, true_and, ite_true]
        simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
          Nat.cast_le] using hover p hp
      · simp [hp]
    _ = (M : ℝ≥0∞) * μ P := lintegral_indicator_const hP _

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
