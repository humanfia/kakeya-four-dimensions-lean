-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GGIsometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.Basic

/-!
# Frozen tube families under linear isometries

Tubes, dilated tubes, volumes and convex sets are carried by a linear isometry of `Space`,
so `Family` and `Separated` are invariant.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace

variable (R : Space ≃ₗᵢ[ℝ] Space)

theorem LinearIsometryEquiv.image_thickening' (δ : ℝ) (S : Set Space) :
    R '' thickening δ S = thickening δ (R '' S) := by
  ext p
  simp only [mem_image, mem_thickening_iff]
  constructor
  · rintro ⟨q, ⟨s, hs, hqs⟩, rfl⟩
    exact ⟨R s, ⟨s, hs, rfl⟩, by rwa [LinearIsometryEquiv.dist_map]⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, hps⟩
    refine ⟨R.symm p, ⟨s, hs, ?_⟩, by simp⟩
    rw [← LinearIsometryEquiv.dist_map R, LinearIsometryEquiv.apply_symm_apply]
    exact hps

theorem LinearIsometryEquiv.image_segment' (x y : Space) :
    R '' segment ℝ x y = segment ℝ (R x) (R y) :=
  image_segment ℝ ((R : Space →ₗ[ℝ] Space).toAffineMap) x y

theorem image_tube (δ : ℝ) (x v : Space) : R '' tube δ x v = tube δ (R x) (R v) := by
  rw [tube, tube, LinearIsometryEquiv.image_thickening', LinearIsometryEquiv.image_segment',
    map_add]

theorem image_dilatedTube (ρ : ℝ) (z w : Space) :
    R '' dilatedTube ρ z w = dilatedTube ρ (R z) (R w) := by
  rw [dilatedTube, dilatedTube, LinearIsometryEquiv.image_thickening',
    LinearIsometryEquiv.image_segment', map_sub, map_add, map_smul, map_smul]

theorem volume_image_isometry (S : Set Space) : volume (R '' S) = volume S := by
  have h := (LinearIsometryEquiv.measurePreserving R.symm).measure_preimage_equiv
    (f := R.symm.toHomeomorph.toMeasurableEquiv) S
  have he : (R.symm.toHomeomorph.toMeasurableEquiv : Space → Space) ⁻¹' S = R '' S := by
    ext p
    simp only [mem_preimage, mem_image]
    constructor
    · intro hp; exact ⟨R.symm p, hp, by simp⟩
    · rintro ⟨q, hq, rfl⟩; simpa using hq
  rw [← he]
  exact h

theorem image_subset_image_iff_isometry {A B : Set Space} : R '' A ⊆ R '' B ↔ A ⊆ B :=
  Set.image_subset_image_iff R.injective

theorem tube_subset_iff_isometry (δ ρ : ℝ) (x v z w : Space) :
    tube δ (R x) (R v) ⊆ tube ρ (R z) (R w) ↔ tube δ x v ⊆ tube ρ z w := by
  rw [← image_tube, ← image_tube, image_subset_image_iff_isometry]

theorem tube_subset_dilated_iff_isometry (δ ρ : ℝ) (x v z w : Space) :
    tube δ (R x) (R v) ⊆ dilatedTube ρ (R z) (R w) ↔ tube δ x v ⊆ dilatedTube ρ z w := by
  rw [← image_tube, ← image_dilatedTube, image_subset_image_iff_isometry]

theorem Family.isometry {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Family η δ n x v Y) :
    Family η δ n (fun i => R (x i)) (fun i => R (v i)) (fun i => R '' Y i) := by
  obtain ⟨hn, hv, hball, hhalf, hYm, hYT, hmass⟩ := h
  refine ⟨hn, fun i => by rw [LinearIsometryEquiv.norm_map]; exact hv i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← image_tube]
    rintro _ ⟨p, hp, rfl⟩
    have := hball i hp
    rw [mem_ball_zero_iff] at this ⊢
    rwa [LinearIsometryEquiv.norm_map]
  · intro i j hij
    rw [← image_tube, ← image_tube, ← Set.image_inter R.injective, volume_image_isometry,
      volume_image_isometry]
    exact hhalf i j hij
  · intro i
    show MeasurableSet (R '' Y i)
    have : R '' Y i = R.symm ⁻¹' Y i := by
      ext p; simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨q, hq, rfl⟩; simpa using hq
      · intro hp; exact ⟨R.symm p, hp, by simp⟩
    rw [this]
    exact R.symm.continuous.measurable (hYm i)
  · intro i
    rw [← image_tube]
    exact Set.image_mono (hYT i)
  · simp only [volume_image_isometry]
    exact hmass

theorem Separated.isometry {η δ : ℝ} {n : ℕ} {x v : Fin n → Space}
    (h : Separated η δ n x v) : Separated η δ n (fun i => R (x i)) (fun i => R (v i)) := by
  intro r hδr hr1
  obtain ⟨ρ, hrρ, hρ1, hρr, k, hk, z, w, hw, hd, hc, ho, hb, hf, hs⟩ := h r hδr hr1
  refine ⟨ρ, hrρ, hρ1, hρr, k, hk, fun j => R (z j), fun j => R (w j),
    fun j => by rw [LinearIsometryEquiv.norm_map]; exact hw j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' hjj
    rw [← image_tube, ← image_tube, ← Set.image_inter R.injective, volume_image_isometry,
      volume_image_isometry]
    exact hd j j' hjj
  · intro i
    simp only [tube_subset_iff_isometry]
    exact hc i
  · intro j
    simp only [tube_subset_iff_isometry]
    exact ho j
  · intro j j'
    simp only [tube_subset_iff_isometry]
    exact hb j j'
  · intro j W hW
    have hW' : Convex ℝ (R.symm '' W) := hW.linear_image (R.symm : Space →ₗ[ℝ] Space)
    have hset : {i | tube δ (R (x i)) (R (v i)) ⊆ tube ρ (R (z j)) (R (w j)) ∧
        tube δ (R (x i)) (R (v i)) ⊆ W} =
        {i | tube δ (x i) (v i) ⊆ tube ρ (z j) (w j) ∧ tube δ (x i) (v i) ⊆ R.symm '' W} := by
      ext i
      simp only [mem_ofPred_eq, tube_subset_iff_isometry]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun p hp => ⟨R p, h2 (by rw [← image_tube]; exact ⟨p, hp, rfl⟩), by simp⟩⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [← image_tube]
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq, hqp⟩ := h2 hp
        rw [← hqp]; simpa using hq
    rw [hset]
    simp only [tube_subset_iff_isometry]
    have hvol : volume (R.symm '' W) = volume W := by
      have := volume_image_isometry R.symm W
      exact this
    rw [← hvol]
    exact hf j _ hW'
  · intro i j j'
    simp only [tube_subset_dilated_iff_isometry]
    exact hs i j j'

/-- A rotation taking a unit vector `u` to `e₀` and a unit vector `w ⊥ u` to `e₂`. -/
theorem exists_rotation {u w : Space} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, R u = EuclideanSpace.single 0 1 ∧
      R w = EuclideanSpace.single 2 1 := by
  set v : Fin 3 → Space := ![u, 0, w] with hv_def
  have hwu : ⟪w, u⟫ = 0 := by rw [real_inner_comm]; exact huw
  have hv : Orthonormal ℝ (({0, 2} : Set (Fin 3)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [v, Set.domRestrict_apply, hu, hw, huw, hwu]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (by simp) hv
  refine ⟨b.repr, ?_, ?_⟩
  · have h0 : b 0 = u := hb 0 (by simp)
    rw [← h0]; exact b.repr_self 0
  · have h2 : b 2 = w := hb 2 (by simp)
    rw [← h2]; exact b.repr_self 2

/-- Coordinates are inner products with the standard basis. -/
theorem coord_eq_inner (p : Space) (i : Fin 3) : p i = ⟪p, EuclideanSpace.single i 1⟫ := by
  simp [EuclideanSpace.inner_single_right]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
