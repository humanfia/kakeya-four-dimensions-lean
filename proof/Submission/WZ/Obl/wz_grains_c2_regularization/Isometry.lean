-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_c2_regularization.Isometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_c2_regularization.Transfer

namespace WangZahlLot.Obl.wz_grains_c2_regularization

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Tube := WangZahlLot.Obl.wz_separated_cover_refinement.Tube
abbrev Dilate := WangZahlLot.Obl.wz_separated_cover_refinement.Dilate

theorem isometry_volume_image (e : Space ≃ₗᵢ[ℝ] Space) (E : Set Space) :
    volume (e '' E) = volume E := by
  have h := e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding (e '' E)
  simpa only [preimage_image_eq _ e.injective] using h.symm

theorem isometry_thickening (e : Space ≃ₗᵢ[ℝ] Space) (d : ℝ) (E : Set Space) :
    thickening d (e '' E) = e '' thickening d E := by
  ext q
  constructor
  · intro hq
    obtain ⟨_, ⟨p, hp, rfl⟩, hdist⟩ := mem_thickening_iff.mp hq
    refine ⟨e.symm q, mem_thickening_iff.mpr ⟨p, hp, ?_⟩, e.apply_symm_apply q⟩
    rw [← e.dist_map (e.symm q) p, e.apply_symm_apply]
    exact hdist
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hdist⟩ := mem_thickening_iff.mp hq
    exact mem_thickening_iff.mpr ⟨e p, ⟨p, hp, rfl⟩, by simpa using hdist⟩

theorem isometry_segment (e : Space ≃ₗᵢ[ℝ] Space) (x y : Space) :
    segment ℝ (e x) (e y) = e '' segment ℝ x y :=
  (image_segment ℝ e.toLinearMap.toAffineMap x y).symm

theorem tube_isometry (e : Space ≃ₗᵢ[ℝ] Space) (d : ℝ) (x v : Space) :
    Tube d (e x) (e v) = e '' Tube d x v := by
  change thickening d (segment ℝ (e x) (e x + e v)) = _
  rw [← map_add, isometry_segment, isometry_thickening]

theorem dilate_isometry (e : Space ≃ₗᵢ[ℝ] Space) (d : ℝ) (x v : Space) :
    Dilate d (e x) (e v) = e '' Dilate d x v := by
  change thickening (10 * d)
    (segment ℝ (e x - (9 / 2 : ℝ) • e v) (e x + (11 / 2 : ℝ) • e v)) = _
  rw [← map_smul, ← map_smul, ← map_sub, ← map_add, isometry_segment, isometry_thickening]

theorem dense_isometry (e : Space ≃ₗᵢ[ℝ] Space) {η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space} (h : Dense η δ n x v Y) :
    Dense η δ n (fun i => e (x i)) (fun i => e (v i)) (fun i => e '' Y i) := by
  obtain ⟨hn, hv, hball, hsep, hmeas, hY, hmass⟩ := h
  refine ⟨hn, (fun i => (e.norm_map _).trans (hv i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change Tube δ (e (x i)) (e (v i)) ⊆ ball 0 1
    rw [tube_isometry]
    rintro _ ⟨p, hp, rfl⟩
    simpa only [mem_ball, dist_zero_right, e.norm_map] using hball i hp
  · intro i j hij
    simpa only [tube_isometry, ← image_inter e.injective, isometry_volume_image] using hsep i j hij
  · intro i
    exact e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr (hmeas i)
  · intro i
    change e '' Y i ⊆ Tube δ (e (x i)) (e (v i))
    rw [tube_isometry]
    exact image_mono (hY i)
  · simpa only [isometry_volume_image] using hmass

theorem coverAt_isometry (e : Space ≃ₗᵢ[ℝ] Space) {δ K ρ : ℝ} {n k : ℕ}
    {x v : Fin n → Space} {z w : Fin k → Space} (h : CoverAt δ K ρ x v z w) :
    CoverAt δ K ρ (fun i => e (x i)) (fun i => e (v i))
      (fun j => e (z j)) (fun j => e (w j)) := by
  obtain ⟨hw, hsep, huniq, hfull, hbal, hconvex⟩ := h
  refine ⟨(fun j => (e.norm_map _).trans (hw j)), ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hjj'
    simpa only [tube_isometry, ← image_inter e.injective, isometry_volume_image]
      using hsep j j' hjj'
  · intro i
    simpa only [tube_isometry, image_subset_image_iff e.injective] using huniq i
  · intro j
    simpa only [tube_isometry, image_subset_image_iff e.injective] using hfull j
  · intro j j'
    simpa only [tube_isometry, image_subset_image_iff e.injective] using hbal j j'
  · intro j W hW
    have h := hconvex j (e ⁻¹' W) (hW.linear_preimage e.toLinearMap)
    have hvol : volume (e ⁻¹' W) = volume W :=
      e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding W
    simpa only [tube_isometry, image_subset_image_iff e.injective, image_subset_iff, hvol] using h

theorem strong_isometry (e : Space ≃ₗᵢ[ℝ] Space) {η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} (h : Strong η δ n x v) :
    Strong η δ n (fun i => e (x i)) (fun i => e (v i)) := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hcover, hsep⟩ := h r hδr hr1
  refine ⟨ρ, hrρ, hρ1, hρr, k, hk, (fun j => e (z j)), (fun j => e (w j)),
    coverAt_isometry e hcover, ?_⟩
  intro i j j' hij hij'
  apply hsep i j j'
  · simpa only [tube_isometry, dilate_isometry, image_subset_image_iff e.injective] using hij
  · simpa only [tube_isometry, dilate_isometry, image_subset_image_iff e.injective] using hij'

theorem ExtremalFamily.isometry (e : Space ≃ₗᵢ[ℝ] Space) {σ η δ : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : ExtremalFamily σ η δ n x v Y) :
    ExtremalFamily σ η δ n (fun i => e (x i)) (fun i => e (v i)) (fun i => e '' Y i) := by
  refine ⟨dense_isometry e h.1, strong_isometry e h.2.1,
    (fun i => (h.2.2.1 i).image e.continuous), ?_⟩
  simpa only [← image_iUnion, isometry_volume_image] using h.2.2.2

/-- An orthogonal change of coordinates transports the local plane field and all
its grain counts. Only the coordinate-dependent global slice estimate must be supplied. -/
theorem Grains.isometry (e : Space ≃ₗᵢ[ℝ] Space) {σ δ K : ℝ} {n : ℕ}
    {v : Fin n → Space} {Y : Fin n → Set Space} {f g : ℝ → ℝ} {P : Space → Space}
    (h : Grains σ δ K v Y f P)
    (hglobal : ∀ z ∈ Icc (-1 : ℝ) 1,
      Assouad δ (1 - σ) K (ProjectedSlice g (⋃ i, e '' Y i) z)) :
    Grains σ δ K (fun i => e (v i)) (fun i => e '' Y i) g
      (fun p => e (P (e.symm p))) := by
  obtain ⟨_, hP, hnorm, horth, hlocal⟩ := h
  have hunion : (⋃ i, e '' Y i) = e '' (⋃ i, Y i) := (image_iUnion ..).symm
  refine ⟨hglobal, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul, Function.comp_def] using e.lipschitzWith.comp (hP.comp e.symm.lipschitzWith)
  · intro p hp
    rw [hunion] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simpa only [e.symm_apply_apply, e.norm_map] using hnorm q hq
  · rintro i _ ⟨p, hp, rfl⟩
    simpa only [e.symm_apply_apply, e.inner_map_map] using horth i p hp
  · intro ρ hδρ hρ1 p hp
    rw [hunion] at hp
    obtain ⟨p, hp, rfl⟩ := hp
    have hball : ball (e p) (Real.sqrt ρ) = e '' ball p (Real.sqrt ρ) :=
      (e.toIsometryEquiv.image_ball p (Real.sqrt ρ)).symm
    rw [hunion, hball, ← image_inter e.injective, image_image]
    simpa only [e.symm_apply_apply, e.inner_map_map] using hlocal ρ hδρ hρ1 p hp

end WangZahlLot.Obl.wz_grains_c2_regularization
