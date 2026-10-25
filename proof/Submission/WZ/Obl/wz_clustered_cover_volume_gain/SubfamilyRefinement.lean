-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.SubfamilyRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketRefinement
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Indexing

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (enumerate enumerate_mem enumerate_surj
  sum_enumerate extendSets extendSets_enumerate extendSets_outside sum_extendSets)

lemma bodyCount_extendSets {n : ℕ} (I : Finset (Fin n)) (W : Fin I.card → Set Space) (p : Space) :
    bodyCount (extendSets I W) p = bodyCount W p := by
  classical
  have he : {i | p ∈ extendSets I W i} = enumerate I '' {j | p ∈ W j} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hp
      have hi : i ∈ I := by
        by_contra h
        rw [extendSets_outside I W h] at hp
        exact hp
      obtain ⟨j, rfl⟩ := enumerate_surj I hi
      exact ⟨j, by rwa [extendSets_enumerate] at hp, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      rwa [extendSets_enumerate]
  change ({i | p ∈ extendSets I W i}.ncard : ℝ) = _
  rw [he, Set.ncard_image_of_injective _ (enumerate I).injective]
  rfl

lemma sum_extendSets_univ {n : ℕ} (I : Finset (Fin n)) (W : Fin I.card → Set Space) :
    ∑ i, volume (extendSets I W i) = ∑ j, volume (W j) := by
  classical
  rw [← sum_extendSets]
  symm
  apply Finset.sum_subset (Finset.subset_univ I)
  intro i _ hi
  rw [extendSets_outside I W hi, measure_empty]

theorem extend_subfamily_refinement {n : ℕ} (I : Finset (Fin n))
    (Y : Fin n → Set Space) (W : Fin I.card → Set Space) {B : ℝ}
    (hW : ∀ j, MeasurableSet (W j) ∧ W j ⊆ Y (enumerate I j))
    (hmass : (1 / 2 : ℝ≥0∞) * ∑ j, volume (Y (enumerate I j)) ≤ ∑ j, volume (W j))
    (hcount : ∀ p, bodyCount W p ≤ B) :
    ∃ Z : Fin n → Set Space,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ (i ∉ I → Z i = ∅)) ∧
      (1 / 2 : ℝ≥0∞) * ∑ i ∈ I, volume (Y i) ≤ ∑ i, volume (Z i) ∧
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

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
