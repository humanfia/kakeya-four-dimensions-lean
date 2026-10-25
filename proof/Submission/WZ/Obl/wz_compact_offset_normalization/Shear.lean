-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_compact_offset_normalization.Shear.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_compact_offset_normalization.Basic

/-!
# The horizontal shear-compression

`shear c p = (sa (p 0 + c p 1), sa p 1, p 2)` with `sa = 1/1000`. For `|c| ≤ 100` it is a
contraction which compresses the horizontal coordinates by a factor `1/40` in square, it has
determinant `sa²`, and it intertwines the projections `P_f` and `P_(f - c)`:

  `P_(f - c) (shear c p) = (sa (p 0 + f (p 2) p 1), p 2)`.
-/

namespace WangZahlLot.Obl.wz_compact_offset_normalization

open Set Metric MeasureTheory
open scoped ENNReal

/-- The horizontal scale of the shear. -/
noncomputable def sa : ℝ := 1 / 1000

theorem sa_pos : 0 < sa := by norm_num [sa]

theorem sa_le_one : sa ≤ 1 := by norm_num [sa]

/-- The matrix of the shear. -/
noncomputable def shearMat (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![sa, sa * c, 0; 0, sa, 0; 0, 0, 1]

/-- The shear-compression as a linear map of `Space`. -/
noncomputable def shear (c : ℝ) : Space →ₗ[ℝ] Space :=
  ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm : (Fin 3 → ℝ) →ₗ[ℝ] Space) ∘ₗ
    Matrix.toLin' (shearMat c) ∘ₗ
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.symm : Space →ₗ[ℝ] (Fin 3 → ℝ))

theorem shear_apply (c : ℝ) (p : Space) :
    shear c p = WithLp.toLp 2 ![sa * (p 0 + c * p 1), sa * p 1, p 2] := by
  ext i
  fin_cases i <;> simp [shear, shearMat, Matrix.toLin'_apply, dotProduct,
    Fin.sum_univ_three] <;> ring

@[simp] theorem shear_apply_zero (c : ℝ) (p : Space) : shear c p 0 = sa * (p 0 + c * p 1) := by
  rw [shear_apply]; simp

@[simp] theorem shear_apply_one (c : ℝ) (p : Space) : shear c p 1 = sa * p 1 := by
  rw [shear_apply]; simp

@[simp] theorem shear_apply_two (c : ℝ) (p : Space) : shear c p 2 = p 2 := by
  rw [shear_apply]; simp

theorem shear_det (c : ℝ) : LinearMap.det (shear c) = sa ^ 2 := by
  unfold shear
  rw [LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fin_three]
  simp [shearMat]
  ring

theorem shear_det_ne_zero (c : ℝ) : LinearMap.det (shear c) ≠ 0 := by
  rw [shear_det]; exact pow_ne_zero 2 sa_pos.ne'

theorem continuous_shear (c : ℝ) : Continuous (shear c) :=
  LinearMap.continuous_of_finiteDimensional _

theorem shear_injective (c : ℝ) : Function.Injective (shear c) := by
  intro p q h
  have h0 := congrArg (fun r : Space => r 0) h
  have h1 := congrArg (fun r : Space => r 1) h
  have h2 := congrArg (fun r : Space => r 2) h
  simp only [shear_apply_zero, shear_apply_one, shear_apply_two] at h0 h1 h2
  have hs := sa_pos.ne'
  have e1 : p 1 = q 1 := mul_left_cancel₀ hs h1
  have e0 : p 0 = q 0 := by
    have := mul_left_cancel₀ hs h0
    rw [e1] at this
    linarith
  ext i
  fin_cases i
  · exact e0
  · exact e1
  · exact h2

/-- The horizontal compression, in squared coordinates. -/
theorem shear_horizontal {c : ℝ} (hc : |c| ≤ 100) (p : Space) :
    shear c p 0 ^ 2 + shear c p 1 ^ 2 ≤ (p 0 ^ 2 + p 1 ^ 2) / 40 := by
  simp only [shear_apply_zero, shear_apply_one, sa]
  have hc2 : c ^ 2 ≤ 10000 := by
    have := sq_abs c
    nlinarith [abs_nonneg c]
  have h1 : (p 0 + c * p 1) ^ 2 ≤ 2 * p 0 ^ 2 + 2 * (c ^ 2 * p 1 ^ 2) := by
    nlinarith [sq_nonneg (p 0 - c * p 1)]
  have h2 : c ^ 2 * p 1 ^ 2 ≤ 10000 * p 1 ^ 2 :=
    mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

theorem shear_norm_sq_le {c : ℝ} (hc : |c| ≤ 100) (p : Space) : ‖shear c p‖ ^ 2 ≤ ‖p‖ ^ 2 := by
  rw [norm_sq_eq, norm_sq_eq, shear_apply_two]
  have := shear_horizontal hc p
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

theorem shear_norm_le {c : ℝ} (hc : |c| ≤ 100) (p : Space) : ‖shear c p‖ ≤ ‖p‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (shear_norm_sq_le hc p)

theorem shear_dist_le {c : ℝ} (hc : |c| ≤ 100) (p q : Space) :
    dist (shear c p) (shear c q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact shear_norm_le hc _

/-- The image of a tube lies in the tube of the image axis. -/
theorem shear_image_tube {c : ℝ} (hc : |c| ≤ 100) (δ : ℝ) (x v : Space) :
    shear c '' Tube δ x v ⊆ Tube δ (shear c x) (shear c v) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  refine mem_tube_iff.mpr ⟨t, ht, ?_⟩
  have : shear c x + t • shear c v = shear c (x + t • v) := by
    rw [map_add, map_smul]
  rw [this]
  exact (shear_dist_le hc _ _).trans_lt hpt

theorem shear_volume_image (c : ℝ) (E : Set Space) :
    volume (shear c '' E) = ENNReal.ofReal (sa ^ 2) * volume E := by
  rw [Measure.addHaar_image_linearMap, shear_det, abs_of_pos (by have := sa_pos; positivity)]

theorem shear_volume_preimage (c : ℝ) (W : Set Space) :
    volume (shear c ⁻¹' W) = ENNReal.ofReal ((sa ^ 2)⁻¹) * volume W := by
  rw [Measure.addHaar_preimage_linearMap _ (shear_det_ne_zero c), shear_det,
    abs_of_pos (by have := sa_pos; positivity)]

theorem shear_measurableSet_image (c : ℝ) {E : Set Space} (hE : MeasurableSet E) :
    MeasurableSet (shear c '' E) :=
  hE.image_of_continuousOn_injOn (continuous_shear c).continuousOn
    (shear_injective c).injOn

theorem shear_convex_preimage (c : ℝ) {W : Set Space} (hW : Convex ℝ W) :
    Convex ℝ (shear c ⁻¹' W) :=
  hW.linear_preimage (shear c)

/-! ### The projection identity -/

/-- The horizontal rescaling of the plane. -/
noncomputable def planeScale : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.prodMap (sa • LinearMap.id) LinearMap.id

theorem planeScale_apply (q : ℝ × ℝ) : planeScale q = (sa * q.1, q.2) := by
  simp [planeScale]

theorem projection_shear (f : ℝ → ℝ) (E : Set Space) :
    Projection (fun z => f z - f 0) (shear (f 0) '' E) = planeScale '' Projection f E := by
  rw [Projection, Projection, image_image, image_image]
  apply image_congr
  intro p _
  rw [planeScale_apply]
  simp only [shear_apply_zero, shear_apply_one, shear_apply_two]
  ext
  · simp only
    ring
  · rfl

theorem volume_planeScale_image_le (X : Set (ℝ × ℝ)) : volume (planeScale '' X) ≤ volume X := by
  rw [Measure.addHaar_image_linearMap]
  have hdet : LinearMap.det planeScale = sa := by
    rw [planeScale, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id,
      Module.finrank_self]
    ring
  rw [hdet, abs_of_pos sa_pos]
  calc ENNReal.ofReal sa * volume X ≤ 1 * volume X := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr sa_le_one
    _ = volume X := one_mul _

end WangZahlLot.Obl.wz_compact_offset_normalization
