-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Containers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabVolume
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.QuantitativeNormalization
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.TubeBodies

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma volume_unit_ball_lower : ENNReal.ofReal (1 / 8 : ℝ) ≤ volume (ball (0 : E) 1) := by
  let ν := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hν : ‖ν‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0
  have h := volume_ball_inter_slab_ge (p := (0 : E)) (s := 0) (r := 1) hν
    (by norm_num) (by norm_num) (by simp)
  calc ENNReal.ofReal (1 / 8 : ℝ)
      ≤ volume (ball (0 : E) 1 ∩ slab (innerSL ℝ ν) 0 1) := by simpa using h
    _ ≤ _ := measure_mono inter_subset_left

lemma volume_ball_lower {r : ℝ} (hr : 0 < r) (x : E) :
    ENNReal.ofReal (r ^ 3 / 8) ≤ volume (ball x r) := by
  rw [Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin]
  calc ENNReal.ofReal (r ^ 3 / 8) = ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (1 / 8 : ℝ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ _ := mul_le_mul_right volume_unit_ball_lower _

lemma volume_unit_closedBall_upper : volume (closedBall (0 : E) 1) ≤ 8 := by
  let ν := EuclideanSpace.basisFun (Fin 3) ℝ 0
  have hν : ‖ν‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.1 0
  have hsub : closedBall (0 : E) 1 ⊆ slab (innerSL ℝ ν) 0 1 := by
    intro p hp
    have hp' : ‖p‖ ≤ 1 := by simpa using hp
    change |inner ℝ ν p - 0| ≤ 1
    simp only [sub_zero]
    exact (abs_real_inner_le_norm _ _).trans (by rw [hν, one_mul]; exact hp')
  have h := volume_ball_inter_slab_le hν 0 (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
  rw [inter_eq_left.mpr hsub] at h
  simpa using h

lemma slab_convex (ℓ : E →L[ℝ] ℝ) (s r : ℝ) : Convex ℝ (slab ℓ s r) := by
  have he : slab ℓ s r = ℓ ⁻¹' Icc (s - r) (s + r) := by
    ext p
    simp only [slab, mem_ofPred_eq, mem_preimage, mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he]
  exact (convex_Icc _ _).linear_preimage ℓ.toLinearMap

lemma affine_image_preimage_inter (f : E ≃ᵃ[ℝ] E) (U V : Set E) :
    f '' (f ⁻¹' U ∩ V) = U ∩ f '' V := by
  ext p
  constructor
  · rintro ⟨q, ⟨hqU, hqV⟩, rfl⟩
    exact ⟨hqU, q, hqV, rfl⟩
  · rintro ⟨hpU, q, hqV, rfl⟩
    exact ⟨q, ⟨hpU, hqV⟩, rfl⟩

/-- Cutting a normalized body by a thin slab reduces its physical volume by a
fixed constant times the slab width. -/
lemma normalized_slab_volume_shrink {U : Set E} {S D r : ℝ} (hS : 0 < S)
    (f : E ≃ᵃ[ℝ] E) (hD : 0 ≤ D)
    (hsmall : f ⁻¹' U ⊆ closedBall (0 : E) (2 / S))
    (hvol : ∀ Q : Set E, volume (f '' Q) = ENNReal.ofReal D * volume Q)
    (hDupper : ENNReal.ofReal D ≤ ENNReal.ofReal (64 * S ^ 3) * volume U)
    {ν : E} (hν : ‖ν‖ = 1) (s : ℝ) (hr : 0 ≤ r) :
    volume (U ∩ f '' slab (innerSL ℝ ν) s r) ≤
      ENNReal.ofReal (2048 * S * r) * volume U := by
  rw [← affine_image_preimage_inter, hvol]
  have hslab := volume_ball_inter_slab_le hν s hr (by positivity : 0 ≤ 2 / S)
  calc ENNReal.ofReal D * volume (f ⁻¹' U ∩ slab (innerSL ℝ ν) s r)
      ≤ ENNReal.ofReal D * volume (closedBall (0 : E) (2 / S) ∩ slab (innerSL ℝ ν) s r) :=
        mul_le_mul_right (measure_mono (inter_subset_inter_left _ hsmall)) _
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (8 * r * (2 / S) ^ 2) := mul_le_mul_right hslab _
    _ ≤ (ENNReal.ofReal (64 * S ^ 3) * volume U) * ENNReal.ofReal (8 * r * (2 / S) ^ 2) :=
      mul_le_mul_left hDupper _
    _ = ENNReal.ofReal (2048 * S * r) * volume U := by
      rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      field_simp
      ring

lemma compact_convex_slab_cut {U : Set E} (hUc : IsCompact U) (hU : Convex ℝ U)
    (f : E ≃ᵃ[ℝ] E) (ν : E) (s r : ℝ) :
    IsCompact (U ∩ f '' slab (innerSL ℝ ν) s r) ∧
    Convex ℝ (U ∩ f '' slab (innerSL ℝ ν) s r) := by
  exact ⟨hUc.inter_right (f.toContinuousAffineEquiv.toHomeomorph.isClosedMap _ (slab_isClosed _ _ _)),
    hU.inter ((slab_convex _ _ _).affine_image f.toAffineMap)⟩

/-- Every container of a whole tube has a positive polynomial volume lower bound. -/
lemma whole_tube_container_volume_lower {δ : ℝ} (hδ : 0 < δ) (x v : E) {U : Set E}
    (hU : closedTube δ x v ⊆ U) : ENNReal.ofReal (δ ^ 3 / 8) ≤ volume U :=
  (volume_ball_lower hδ x).trans (measure_mono
    (((ball_subset_tube x v).trans (tube_subset_closedTube δ x v)).trans hU))

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
