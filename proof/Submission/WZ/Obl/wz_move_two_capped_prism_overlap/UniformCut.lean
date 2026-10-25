-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.UniformCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, UniformCut.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V O bodyCount bodyCount_inter body_mass_le_of_count body_mass_le_mul_of_count)

/-- A volume refinement transfers to incidence mass when the multiplicity
on the original union is comparable. The cut is common to all fine tubes,
so it also preserves their pointwise angular proportions. -/
theorem uniform_cut_retains_mass {n : ℕ} (W : Fin n → Set V)
    (hWm : ∀ i, MeasurableSet (W i)) (C : Set V) (hCm : MeasurableSet C)
    (hCH : C ⊆ ⋃ i, W i) {m t : ℝ} (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hlevel : ∀ p ∈ ⋃ i, W i, m ≤ bodyCount W p ∧ bodyCount W p ≤ 2 * m)
    (hretain : O t * volume (⋃ i, W i) ≤ volume C) :
    O (t / 2) * ∑ i, volume (W i) ≤ ∑ i, volume (W i ∩ C) := by
  classical
  let H := ⋃ i, W i
  have hHm : MeasurableSet H := MeasurableSet.iUnion hWm
  have horig : ∑ i, volume (W i) ≤ O (2 * m) * volume H := by
    have hh := body_mass_le_mul_of_count hWm (fun _ : Fin 1 => hHm)
      (show 0 ≤ 2 * m by positivity) (fun p => ?_)
    · simpa only [Fin.sum_univ_one] using hh
    · by_cases hp : p ∈ H
      · simpa [bodyCount, hp] using (hlevel p hp).2
      · have hempty : {i | p ∈ W i} = ∅ := by
          ext i
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun hi => hp (mem_iUnion.mpr ⟨i, hi⟩)
        simp [bodyCount, hempty, hp]
  have hnew : O m * volume C ≤ ∑ i, volume (W i ∩ C) := by
    have hh := body_mass_le_of_count (fun _ : Fin 1 => hCm)
      (fun i => (hWm i).inter hCm) hm (fun p => ?_)
    · simpa only [Fin.sum_univ_one] using hh
    · rw [bodyCount_inter]
      by_cases hp : p ∈ C
      · simpa [bodyCount, hp] using (hlevel p (hCH hp)).1
      · simp [bodyCount, hp]
  calc
    _ ≤ O (t / 2) * (O (2 * m) * volume H) := mul_le_mul' le_rfl horig
    _ = O m * (O t * volume H) := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ t / 2),
        ← ENNReal.ofReal_mul hm]
      congr 2
      ring
    _ ≤ O m * volume C := mul_le_mul' le_rfl hretain
    _ ≤ _ := hnew

/-- The multiplicity level can vary from prism to prism: only the common
factor-two comparison is needed for the total incidence mass. -/
theorem uniform_prism_cut_retains_mass {n L : ℕ} (W : Fin n → Fin L → Set V)
    (hWm : ∀ i j, MeasurableSet (W i j)) (C : Fin L → Set V)
    (hCm : ∀ j, MeasurableSet (C j)) (hCH : ∀ j, C j ⊆ ⋃ i, W i j)
    (m : Fin L → ℝ) (hm : ∀ j, 0 ≤ m j) {t : ℝ} (ht : 0 ≤ t)
    (hlevel : ∀ j p, p ∈ ⋃ i, W i j →
      m j ≤ bodyCount (fun i => W i j) p ∧ bodyCount (fun i => W i j) p ≤ 2 * m j)
    (hretain : ∀ j, O t * volume (⋃ i, W i j) ≤ volume (C j)) :
    O (t / 2) * (∑ i, ∑ j, volume (W i j)) ≤ ∑ i, ∑ j, volume (W i j ∩ C j) := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => volume (W i j ∩ C j)), Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => uniform_cut_retains_mass (fun i => W i j)
    (fun i => hWm i j) (C j) (hCm j) (hCH j) (hm j) ht (hlevel j) (hretain j)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
