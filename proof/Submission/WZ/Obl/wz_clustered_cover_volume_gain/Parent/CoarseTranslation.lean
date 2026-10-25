-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.CoarseTranslation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.CoarseStability
import Submission.WZ.Obl.wz_nsp_translation_model.Counting

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open wz_concentrated_convex_factorization (count density coefficient Upper)

private theorem count_translation_preimage {ι : Type*} [DecidableEq ι]
    (T : ι → Set Space) (S : Finset ι) (z : Space) (W : Set Space) :
    count (fun i => (fun p => p + z) '' T i) S W =
      count T S ((fun p => p + z) ⁻¹' W) := by
  classical
  unfold count
  congr 1
  ext i
  simp only [Finset.mem_filter, Set.image_subset_iff]

theorem count_image_translation {ι : Type*} [DecidableEq ι]
    (T : ι → Set Space) (S : Finset ι) (z : Space) (W : Set Space) :
    count (fun i => (fun p => p + z) '' T i) S ((fun p => p + z) '' W) = count T S W := by
  rw [count_translation_preimage,
    Set.preimage_image_eq _ (show Function.Injective (fun p : Space => p + z) from
      fun _ _ h => add_right_cancel h)]

theorem volume_image_translation (W : Set Space) (z : Space) :
    volume ((fun p => p + z) '' W) = volume W := by
  have he : (fun p => p + z) '' W = (fun p => p + -z) ⁻¹' W := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      exact ⟨p + -z, hp, by simp⟩
  rw [he, measure_preimage_add_right]

/-- Translating every member of a family preserves every convex-count upper constant. -/
theorem upper_image_translation {ι : Type*} [DecidableEq ι] {T : ι → Set Space}
    {r c : ℝ} {S : Finset ι} (h : Upper T r S c) (z : Space) :
    Upper (fun i => (fun p => p + z) '' T i) r S c := by
  intro W hW
  have hh := h ((fun p => p + z) ⁻¹' W)
    (hW.affine_preimage (AffineEquiv.vaddConst ℝ z).toAffineMap)
  rw [measure_preimage_add_right] at hh
  simpa only [count_translation_preimage] using hh

/-- The variational coefficient is exactly invariant under a common translation. -/
theorem coefficient_image_translation {ι : Type*} [DecidableEq ι]
    (T : ι → Set Space) (r : ℝ) (S : Finset ι) (z : Space) :
    coefficient (fun i => (fun p => p + z) '' T i) r S = coefficient T r S := by
  have hd (W : Set Space) :
      density (fun i => (fun p => p + z) '' T i) r S W =
        density T r S ((fun p => p + z) ⁻¹' W) := by
    simp only [density, count_translation_preimage, measure_preimage_add_right]
  have hinj : Function.Injective (fun p : Space => p + z) := fun _ _ h => add_right_cancel h
  unfold coefficient
  congr 1
  ext a
  simp only [mem_insert_iff, mem_ofPred_eq]
  constructor
  · rintro (rfl | ⟨W, hW, ha⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨(fun p => p + z) ⁻¹' W,
        hW.affine_preimage (AffineEquiv.vaddConst ℝ z).toAffineMap, by rwa [hd] at ha⟩
  · rintro (rfl | ⟨W, hW, ha⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨(fun p => p + z) '' W,
        hW.affine_image (AffineEquiv.vaddConst ℝ z).toAffineMap, ?_⟩
      rw [hd, Set.preimage_image_eq _ hinj]
      exact ha

/-- Translation of tube basepoints leaves the coefficient unchanged. -/
theorem coefficient_tube_translation {ι : Type*} [DecidableEq ι]
    (ρ : ℝ) (y w : ι → Space) (S : Finset ι) (z : Space) :
    coefficient (fun k => Tube ρ (y k + z) (w k)) (ρ ^ 2) S =
      coefficient (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) S := by
  simp only [wz_nsp_translation_model.tube_translate]
  exact coefficient_image_translation _ _ _ _

/-- The same translation transports the upper convex count of a tube subfamily. -/
theorem upper_tube_translation {ι : Type*} [DecidableEq ι]
    {ρ c : ℝ} {y w : ι → Space} {S : Finset ι}
    (h : Upper (fun k => Tube ρ (y k) (w k)) (ρ ^ 2) S c) (z : Space) :
    Upper (fun k => Tube ρ (y k + z) (w k)) (ρ ^ 2) S c := by
  simpa only [wz_nsp_translation_model.tube_translate] using upper_image_translation h z

/-- A common translated unit ball is enough for a centered family of exact unit tubes. -/
theorem translated_tube_in_unit_ball {ρ : ℝ} {y w z : Space}
    (h : Tube ρ y w ⊆ Metric.ball z 1) :
    Tube ρ (y + -z) w ⊆ Metric.ball 0 1 := by
  have ht : Tube ρ (y + -z) w = (fun p : Space => p + -z) '' Tube ρ y w :=
    wz_nsp_translation_model.tube_translate ρ y w (-z)
  rw [ht]
  rintro _ ⟨p, hp, rfl⟩
  have hdist := h hp
  simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg] using hdist

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
