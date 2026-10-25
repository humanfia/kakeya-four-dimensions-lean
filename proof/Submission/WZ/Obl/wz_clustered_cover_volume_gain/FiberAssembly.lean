-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.FiberAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SubfamilyRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (enumerate enumerate_mem enumerate_surj
  sum_enumerate extendSets extendSets_enumerate extendSets_outside)

theorem extend_subfamily_mass_count {n : ℕ} (I : Finset (Fin n))
    (Y : Fin n → Set Space) (W : Fin I.card → Set Space) {B : ℝ} {t : ℝ≥0∞}
    (hW : ∀ j, MeasurableSet (W j) ∧ W j ⊆ Y (enumerate I j))
    (hmass : t * ∑ j, volume (Y (enumerate I j)) ≤ ∑ j, volume (W j))
    (hcount : ∀ p, bodyCount W p ≤ B) :
    ∃ Z : Fin n → Set Space,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ I → Z i = ∅)) ∧
      t * ∑ i ∈ I, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ B := by
  classical
  refine ⟨extendSets I W, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ I
    · obtain ⟨j, rfl⟩ := enumerate_surj I hi
      rw [extendSets_enumerate]
      exact ⟨(hW j).1, (hW j).2, fun h => (h (enumerate_mem I j)).elim⟩
    · rw [extendSets_outside I W hi]
      exact ⟨MeasurableSet.empty, empty_subset _, fun _ => rfl⟩
  · rw [sum_extendSets_univ]
    rwa [sum_enumerate I (fun i => volume (Y i))] at hmass
  · intro p
    rw [bodyCount_extendSets]
    exact hcount p

/-- Stitch independently refined coarse fibres while retaining the same mass
fraction and their separate pointwise count bounds. -/
theorem combine_fiber_refinements {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set Space)
    {B : ℝ} {t : ℝ≥0∞}
    (hrefine : ∀ k : Fin N, ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Y i ∧ (f i ≠ k → W i = ∅)) ∧
      t * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)) ≤
        ∑ i, volume (W i) ∧
      ∀ p, bodyCount W p ≤ B) :
    ∃ Z : Fin n → Set Space, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      t * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) ∧
      ∀ k p, fiberBodyCount f Z k p ≤ B := by
  classical
  choose W hW hmass hcount using hrefine
  let Z := fun i => W (f i) i
  have hsum (k : Fin N) : ∑ i, volume (W k i) =
      ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f i = k
    · simp [hi, Z]
    · simp [hi, (hW k i).2.2 hi]
  refine ⟨Z, fun i => ⟨(hW (f i) i).1, (hW (f i) i).2.1⟩, ?_, ?_⟩
  · calc
      _ = ∑ k, t * (∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Y i)) := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise]
      _ ≤ ∑ k, ∑ i, volume (W k i) := Finset.sum_le_sum fun k _ => hmass k
      _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), volume (Z i) := by simp only [hsum]
      _ = _ := Finset.sum_fiberwise _ _ _
  · intro k p
    have he : {i : Fin n | f i = k ∧ p ∈ Z i} = {i : Fin n | p ∈ W k i} := by
      ext i
      change (f i = k ∧ p ∈ Z i) ↔ p ∈ W k i
      constructor
      · rintro ⟨hi, hp⟩
        simpa only [Z, hi] using hp
      · intro hp
        have hi : f i = k := by
          by_contra hne
          simpa only [(hW k i).2.2 hne, mem_empty_iff_false] using hp
        exact ⟨hi, by simpa only [Z, hi] using hp⟩
    rw [fiberBodyCount_eq_ncard, he]
    exact hcount k p

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
