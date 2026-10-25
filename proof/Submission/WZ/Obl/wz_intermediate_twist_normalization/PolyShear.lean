-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.PolyShear.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_compact_offset_normalization.Basic

/-!
# A shear-compression adapted to an arbitrary offset

`pshear c p = (a (p 0 + c p 1), a p 1, p 2)` with `a = psa c = 1 / (1000 (1 + |c|))`.
For every `c` it is a contraction which compresses the horizontal coordinates by a factor
`1/40` in square, it has determinant `a²`, and it intertwines the projections `P_f` and
`P_(f - c)`:

  `P_(f - c) (pshear c p) = (a (p 0 + f (p 2) p 1), p 2)`.

This is the shear of `wz_compact_offset_normalization` with a scale depending on the offset,
so that all losses are polynomial in `1 + |c|`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_compact_offset_normalization (Space Tube Projection mem_tube_iff)

/-- The horizontal scale of the shear. -/
noncomputable def psa (c : ℝ) : ℝ := 1 / (1000 * (1 + |c|))

theorem psa_pos (c : ℝ) : 0 < psa c := by
  unfold psa
  have := abs_nonneg c
  positivity

theorem psa_le_one (c : ℝ) : psa c ≤ 1 := by
  unfold psa
  rw [div_le_one (by have := abs_nonneg c; positivity)]
  have := abs_nonneg c
  nlinarith

theorem psa_mul (c : ℝ) : psa c * (1000 * (1 + |c|)) = 1 := by
  unfold psa
  have : 0 < 1000 * (1 + |c|) := by have := abs_nonneg c; positivity
  field_simp

/-- The matrix of the shear. -/
noncomputable def pshearMat (c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![psa c, psa c * c, 0; 0, psa c, 0; 0, 0, 1]

/-- The shear-compression as a linear map of `Space`. -/
noncomputable def pshear (c : ℝ) : Space →ₗ[ℝ] Space :=
  ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm : (Fin 3 → ℝ) →ₗ[ℝ] Space) ∘ₗ
    Matrix.toLin' (pshearMat c) ∘ₗ
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.symm : Space →ₗ[ℝ] (Fin 3 → ℝ))

theorem pshear_apply (c : ℝ) (p : Space) :
    pshear c p = WithLp.toLp 2 ![psa c * (p 0 + c * p 1), psa c * p 1, p 2] := by
  ext i
  fin_cases i <;> simp [pshear, pshearMat, Matrix.toLin'_apply, dotProduct,
    Fin.sum_univ_three] <;> ring

@[simp] theorem pshear_apply_zero (c : ℝ) (p : Space) :
    pshear c p 0 = psa c * (p 0 + c * p 1) := by
  rw [pshear_apply]; simp

@[simp] theorem pshear_apply_one (c : ℝ) (p : Space) : pshear c p 1 = psa c * p 1 := by
  rw [pshear_apply]; simp

@[simp] theorem pshear_apply_two (c : ℝ) (p : Space) : pshear c p 2 = p 2 := by
  rw [pshear_apply]; simp

theorem pshear_det (c : ℝ) : LinearMap.det (pshear c) = psa c ^ 2 := by
  unfold pshear
  rw [LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fin_three]
  simp [pshearMat]
  ring

theorem pshear_det_ne_zero (c : ℝ) : LinearMap.det (pshear c) ≠ 0 := by
  rw [pshear_det]; exact pow_ne_zero 2 (psa_pos c).ne'

theorem continuous_pshear (c : ℝ) : Continuous (pshear c) :=
  LinearMap.continuous_of_finiteDimensional _

theorem pshear_injective (c : ℝ) : Function.Injective (pshear c) := by
  intro p q h
  have h0 := congrArg (fun r : Space => r 0) h
  have h1 := congrArg (fun r : Space => r 1) h
  have h2 := congrArg (fun r : Space => r 2) h
  simp only [pshear_apply_zero, pshear_apply_one, pshear_apply_two] at h0 h1 h2
  have hs := (psa_pos c).ne'
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

/-- The horizontal compression, in squared coordinates, for every offset. -/
theorem pshear_horizontal (c : ℝ) (p : Space) :
    pshear c p 0 ^ 2 + pshear c p 1 ^ 2 ≤ (p 0 ^ 2 + p 1 ^ 2) / 40 := by
  simp only [pshear_apply_zero, pshear_apply_one]
  set a := psa c with ha
  set m := 1 + |c| with hm
  have hm1 : 1 ≤ m := by have := abs_nonneg c; linarith
  have ham : a * (1000 * m) = 1 := psa_mul c
  have ha0 : 0 < a := psa_pos c
  have hc2 : c ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg c) (by linarith) 2
  have h1 : (p 0 + c * p 1) ^ 2 ≤ 2 * p 0 ^ 2 + 2 * (c ^ 2 * p 1 ^ 2) := by
    nlinarith [sq_nonneg (p 0 - c * p 1)]
  have h2 : c ^ 2 * p 1 ^ 2 ≤ m ^ 2 * p 1 ^ 2 :=
    mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have h4 : p 0 ^ 2 ≤ m ^ 2 * p 0 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hm2
  have h5 : p 1 ^ 2 ≤ m ^ 2 * p 1 ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hm2
  have h6 : 0 ≤ m ^ 2 * p 0 ^ 2 := by positivity
  have h3 : (p 0 + c * p 1) ^ 2 + p 1 ^ 2 ≤ 3 * m ^ 2 * (p 0 ^ 2 + p 1 ^ 2) := by
    nlinarith
  have ham2 : a ^ 2 * m ^ 2 = 1 / 1000000 := by
    have : (a * m) = 1 / 1000 := by linarith
    calc a ^ 2 * m ^ 2 = (a * m) ^ 2 := by ring
      _ = 1 / 1000000 := by rw [this]; norm_num
  have hP : 0 ≤ p 0 ^ 2 + p 1 ^ 2 := by positivity
  calc (a * (p 0 + c * p 1)) ^ 2 + (a * p 1) ^ 2
      = a ^ 2 * ((p 0 + c * p 1) ^ 2 + p 1 ^ 2) := by ring
    _ ≤ a ^ 2 * (3 * m ^ 2 * (p 0 ^ 2 + p 1 ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg a)
    _ = 3 * (a ^ 2 * m ^ 2) * (p 0 ^ 2 + p 1 ^ 2) := by ring
    _ = 3 / 1000000 * (p 0 ^ 2 + p 1 ^ 2) := by rw [ham2]; ring
    _ ≤ (p 0 ^ 2 + p 1 ^ 2) / 40 := by nlinarith

theorem pshear_norm_sq_le (c : ℝ) (p : Space) : ‖pshear c p‖ ^ 2 ≤ ‖p‖ ^ 2 := by
  rw [WangZahlLot.Obl.wz_compact_offset_normalization.norm_sq_eq,
    WangZahlLot.Obl.wz_compact_offset_normalization.norm_sq_eq, pshear_apply_two]
  have := pshear_horizontal c p
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]

theorem pshear_norm_le (c : ℝ) (p : Space) : ‖pshear c p‖ ≤ ‖p‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (pshear_norm_sq_le c p)

theorem pshear_dist_le (c : ℝ) (p q : Space) :
    dist (pshear c p) (pshear c q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact pshear_norm_le c _

/-- The image of a tube lies in the tube of the image axis. -/
theorem pshear_image_tube (c δ : ℝ) (x v : Space) :
    pshear c '' Tube δ x v ⊆ Tube δ (pshear c x) (pshear c v) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨t, ht, hpt⟩ := mem_tube_iff.mp hp
  refine mem_tube_iff.mpr ⟨t, ht, ?_⟩
  have : pshear c x + t • pshear c v = pshear c (x + t • v) := by
    rw [map_add, map_smul]
  rw [this]
  exact (pshear_dist_le c _ _).trans_lt hpt

theorem pshear_volume_image (c : ℝ) (E : Set Space) :
    volume (pshear c '' E) = ENNReal.ofReal (psa c ^ 2) * volume E := by
  rw [Measure.addHaar_image_linearMap, pshear_det,
    abs_of_pos (by have := psa_pos c; positivity)]

theorem pshear_volume_preimage (c : ℝ) (W : Set Space) :
    volume (pshear c ⁻¹' W) = ENNReal.ofReal ((psa c ^ 2)⁻¹) * volume W := by
  rw [Measure.addHaar_preimage_linearMap _ (pshear_det_ne_zero c), pshear_det,
    abs_of_pos (by have := psa_pos c; positivity)]

theorem pshear_measurableSet_image (c : ℝ) {E : Set Space} (hE : MeasurableSet E) :
    MeasurableSet (pshear c '' E) :=
  hE.image_of_continuousOn_injOn (continuous_pshear c).continuousOn
    (pshear_injective c).injOn

theorem pshear_convex_preimage (c : ℝ) {W : Set Space} (hW : Convex ℝ W) :
    Convex ℝ (pshear c ⁻¹' W) :=
  hW.linear_preimage (pshear c)

/-! ### The projection identity -/

/-- The horizontal rescaling of the plane by `psa c`. -/
noncomputable def pplaneScale (c : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.prodMap (psa c • LinearMap.id) LinearMap.id

theorem pplaneScale_apply (c : ℝ) (q : ℝ × ℝ) : pplaneScale c q = (psa c * q.1, q.2) := by
  simp [pplaneScale]

theorem projection_pshear (f : ℝ → ℝ) (E : Set Space) :
    Projection (fun z => f z - f 0) (pshear (f 0) '' E) =
      pplaneScale (f 0) '' Projection f E := by
  rw [Projection, Projection, image_image, image_image]
  apply image_congr
  intro p _
  rw [pplaneScale_apply]
  simp only [pshear_apply_zero, pshear_apply_one, pshear_apply_two]
  ext
  · simp only
    ring
  · rfl

theorem volume_pplaneScale_image_le (c : ℝ) (X : Set (ℝ × ℝ)) :
    volume (pplaneScale c '' X) ≤ volume X := by
  rw [Measure.addHaar_image_linearMap]
  have hdet : LinearMap.det (pplaneScale c) = psa c := by
    rw [pplaneScale, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id,
      Module.finrank_self]
    ring
  rw [hdet, abs_of_pos (psa_pos c)]
  calc ENNReal.ofReal (psa c) * volume X ≤ 1 * volume X := by
        gcongr
        exact ENNReal.ofReal_le_one.mpr (psa_le_one c)
    _ = volume X := one_mul _

end WangZahlLot.Obl.wz_intermediate_twist_normalization
