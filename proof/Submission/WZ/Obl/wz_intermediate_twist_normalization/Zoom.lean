-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.Zoom.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.MidDefs
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Energy
import Submission.WZ.Obl.wz_small_twist_projection_estimate.Pairs

/-!
# The zoom of a class of tubes

For a scale `Z > 0`, an offset `c` and a reference line `α + β z` of the coordinate
`Xc c p = p 0 / c + p 1`, the zoom

  `zoom Z c α β p = (Z (p 0 + c p 1 - c (α + β p 2)), Z (p 1 - (α + β p 2)), p 2)`

is an affine bijection with determinant `Z²` which intertwines `P_f` with `P_(f - c)`:

  `P_(f - c) (zoom p) = (Z (u - f(z) (α + β z)), z)` where `(u, z) = P_f p`.

The fibres of `P_(f - c)` over the zoomed set are the fibres of `P_f`, rescaled by `Z`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN proj lineAt ctr Xc fib
  measurable_fib)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib ofTwist_zero ofTwist_one
  ofTwist_two)

/-- Points of `Space` agree when their three coordinates agree. -/
theorem space_ext3 {p q : Space} (h0 : p 0 = q 0) (h1 : p 1 = q 1) (h2 : p 2 = q 2) :
    p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The matrix of the linear part of the zoom. -/
noncomputable def zmat (Z c β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Z, Z * c, -(Z * c * β); 0, Z, -(Z * β); 0, 0, 1]

/-- The linear part of the zoom. -/
noncomputable def zlin (Z c β : ℝ) : Space →ₗ[ℝ] Space :=
  ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm : (Fin 3 → ℝ) →ₗ[ℝ] Space) ∘ₗ
    Matrix.toLin' (zmat Z c β) ∘ₗ
      ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.symm : Space →ₗ[ℝ] (Fin 3 → ℝ))

theorem zlin_apply (Z c β : ℝ) (p : Space) :
    zlin Z c β p = WithLp.toLp 2 ![Z * (p 0 + c * p 1 - c * β * p 2), Z * (p 1 - β * p 2), p 2] := by
  ext i
  fin_cases i <;> simp [zlin, zmat, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_three] <;> ring

@[simp] theorem zlin_apply_zero (Z c β : ℝ) (p : Space) :
    zlin Z c β p 0 = Z * (p 0 + c * p 1 - c * β * p 2) := by
  rw [zlin_apply]; simp

@[simp] theorem zlin_apply_one (Z c β : ℝ) (p : Space) :
    zlin Z c β p 1 = Z * (p 1 - β * p 2) := by
  rw [zlin_apply]; simp

@[simp] theorem zlin_apply_two (Z c β : ℝ) (p : Space) : zlin Z c β p 2 = p 2 := by
  rw [zlin_apply]; simp

theorem zlin_det (Z c β : ℝ) : LinearMap.det (zlin Z c β) = Z ^ 2 := by
  unfold zlin
  rw [LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_fin_three]
  simp [zmat]
  ring

theorem zlin_det_ne_zero {Z : ℝ} (hZ : Z ≠ 0) (c β : ℝ) : LinearMap.det (zlin Z c β) ≠ 0 := by
  rw [zlin_det]; exact pow_ne_zero 2 hZ

/-- The translation part of the zoom. -/
noncomputable def zshift (Z c α : ℝ) : Space := WithLp.toLp 2 ![Z * c * α, Z * α, 0]

/-- The zoom. -/
noncomputable def zoom (Z c α β : ℝ) (p : Space) : Space := zlin Z c β p - zshift Z c α

@[simp] theorem zoom_apply_zero (Z c α β : ℝ) (p : Space) :
    zoom Z c α β p 0 = Z * (p 0 + c * p 1 - c * (α + β * p 2)) := by
  simp [zoom, zshift]; ring

@[simp] theorem zoom_apply_one (Z c α β : ℝ) (p : Space) :
    zoom Z c α β p 1 = Z * (p 1 - (α + β * p 2)) := by
  simp [zoom, zshift]; ring

@[simp] theorem zoom_apply_two (Z c α β : ℝ) (p : Space) : zoom Z c α β p 2 = p 2 := by
  simp [zoom, zshift]

theorem zoom_sub (Z c α β : ℝ) (p q : Space) :
    zoom Z c α β p - zoom Z c α β q = zlin Z c β (p - q) := by
  simp only [zoom, map_sub]
  abel

theorem zoom_add (Z c α β : ℝ) (p w : Space) :
    zoom Z c α β (p + w) = zoom Z c α β p + zlin Z c β w := by
  simp only [zoom, map_add]
  abel

theorem zoom_injective {Z : ℝ} (hZ : Z ≠ 0) (c α β : ℝ) : Function.Injective (zoom Z c α β) := by
  intro p q h
  have h0 := congrArg (fun r : Space => r 0) h
  have h1 := congrArg (fun r : Space => r 1) h
  have h2 := congrArg (fun r : Space => r 2) h
  simp only [zoom_apply_zero, zoom_apply_one, zoom_apply_two] at h0 h1 h2
  have e1 : p 1 = q 1 := by
    have := mul_left_cancel₀ hZ h1
    rw [h2] at this
    linarith
  have e0 : p 0 = q 0 := by
    have := mul_left_cancel₀ hZ h0
    rw [h2, e1] at this
    linarith
  exact space_ext3 e0 e1 h2

theorem continuous_zlin (Z c β : ℝ) : Continuous (zlin Z c β) :=
  LinearMap.continuous_of_finiteDimensional _

theorem continuous_zoom (Z c α β : ℝ) : Continuous (zoom Z c α β) :=
  (continuous_zlin Z c β).sub continuous_const

theorem zoom_preimage_eq (Z c α β : ℝ) (W : Set Space) :
    zoom Z c α β ⁻¹' W = zlin Z c β ⁻¹' ((fun w => w - zshift Z c α) ⁻¹' W) := by
  ext p; simp [zoom]

theorem zoom_volume_preimage {Z : ℝ} (hZ : 0 < Z) (c α β : ℝ) (W : Set Space) :
    volume (zoom Z c α β ⁻¹' W) = ENNReal.ofReal ((Z ^ 2)⁻¹) * volume W := by
  rw [zoom_preimage_eq, Measure.addHaar_preimage_linearMap _ (zlin_det_ne_zero hZ.ne' c β),
    zlin_det, abs_of_pos (by positivity)]
  congr 1
  simp_rw [sub_eq_add_neg]
  exact measure_preimage_add_right _ _ _

theorem zoom_image_eq (Z c α β : ℝ) (E : Set Space) :
    zoom Z c α β '' E = (fun w => w - zshift Z c α) '' (zlin Z c β '' E) := by
  rw [image_image]; rfl

theorem zoom_volume_image {Z : ℝ} (hZ : 0 < Z) (c α β : ℝ) (E : Set Space) :
    volume (zoom Z c α β '' E) = ENNReal.ofReal (Z ^ 2) * volume E := by
  rw [zoom_image_eq]
  simp_rw [sub_eq_add_neg]
  rw [Set.image_add_right, measure_preimage_add_right, Measure.addHaar_image_linearMap, zlin_det,
    abs_of_pos (by positivity)]

theorem zoom_measurableSet_image {Z : ℝ} (hZ : Z ≠ 0) (c α β : ℝ) {E : Set Space}
    (hE : MeasurableSet E) : MeasurableSet (zoom Z c α β '' E) :=
  hE.image_of_continuousOn_injOn (continuous_zoom Z c α β).continuousOn
    (zoom_injective hZ c α β).injOn

theorem zoom_convex_preimage (Z c α β : ℝ) {W : Set Space} (hW : Convex ℝ W) :
    Convex ℝ (zoom Z c α β ⁻¹' W) := by
  intro p hp q hq a b ha hb hab
  simp only [mem_preimage] at hp hq ⊢
  have he : zoom Z c α β (a • p + b • q) = a • zoom Z c α β p + b • zoom Z c α β q := by
    calc zoom Z c α β (a • p + b • q)
        = a • zlin Z c β p + b • zlin Z c β q - (a + b) • zshift Z c α := by
          rw [hab, one_smul, zoom, map_add, map_smul, map_smul]
      _ = a • zoom Z c α β p + b • zoom Z c α β q := by
          rw [zoom, zoom, add_smul, smul_sub, smul_sub]
          abel
  rw [he]
  exact hW hp hq ha hb hab

/-! ### Projections and fibres -/

/-- The zoom intertwines the twisted projections. -/
theorem zoom_proj_fst (f : ℝ → ℝ) (Z α β : ℝ) (p : Space) :
    zoom Z (f 0) α β p 0 + (f (p 2) - f 0) * zoom Z (f 0) α β p 1 =
      Z * ((p 0 + f (p 2) * p 1) - f (p 2) * (α + β * p 2)) := by
  simp only [zoom_apply_zero, zoom_apply_one]
  ring

/-- The zoom of a twisted point. -/
theorem zoom_ofTwist (f : ℝ → ℝ) {Z : ℝ} (hZ : Z ≠ 0) (α β u' y' z : ℝ) :
    zoom Z (f 0) α β (ofTwist f (u' / Z + f z * (α + β * z)) (y' / Z + (α + β * z)) z) =
      ofTwist (fun w => f w - f 0) u' y' z := by
  apply space_ext3
  · simp only [zoom_apply_zero, ofTwist_zero, ofTwist_one, ofTwist_two]
    field_simp
    ring
  · simp only [zoom_apply_one, ofTwist_zero, ofTwist_one, ofTwist_two]
    field_simp
    ring
  · simp only [zoom_apply_two, ofTwist_two]

/-- The fibres of the zoomed set are rescaled fibres. -/
theorem grainFib_zoom_image (f : ℝ → ℝ) {Z : ℝ} (hZ : Z ≠ 0) (α β : ℝ) (A : Set Space)
    (u' z : ℝ) :
    grainFib (fun w => f w - f 0) (zoom Z (f 0) α β '' A) u' z =
      (fun y' => y' / Z + (α + β * z)) ⁻¹' grainFib f A (u' / Z + f z * (α + β * z)) z := by
  ext y'
  simp only [grainFib, mem_setOf_eq, mem_preimage]
  rw [← zoom_ofTwist f hZ α β u' y' z]
  exact (zoom_injective hZ _ α β).mem_set_image

theorem volume_preimage_affine {Z : ℝ} (hZ : 0 < Z) (a : ℝ) (S : Set ℝ) :
    volume ((fun y' => y' / Z + a) ⁻¹' S) = ENNReal.ofReal Z * volume S := by
  have he : (fun y' => y' / Z + a) ⁻¹' S = (fun y' => Z⁻¹ * y') ⁻¹' ((fun y => y + a) ⁻¹' S) := by
    ext y; simp [div_eq_inv_mul]
  rw [he, Real.volume_preimage_mul_left (inv_ne_zero hZ.ne'), inv_inv, abs_of_pos hZ,
    measure_preimage_add_right]

/-- Fibre lengths of the zoomed set. -/
theorem volume_grainFib_zoom_image (f : ℝ → ℝ) {Z : ℝ} (hZ : 0 < Z) (α β : ℝ) (A : Set Space)
    (u' z : ℝ) :
    volume (grainFib (fun w => f w - f 0) (zoom Z (f 0) α β '' A) u' z) =
      ENNReal.ofReal Z * volume (grainFib f A (u' / Z + f z * (α + β * z)) z) := by
  rw [grainFib_zoom_image f hZ.ne', volume_preimage_affine hZ]

/-- The plane map undoing the zoom on projections. -/
noncomputable def unzoom (f : ℝ → ℝ) (Z α β : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 / Z + f q.2 * (α + β * q.2), q.2)

theorem unzoom_proj {f : ℝ → ℝ} {Z : ℝ} (hZ : Z ≠ 0) (α β : ℝ) (p : Space) :
    unzoom f Z α β (zoom Z (f 0) α β p 0 + (f (zoom Z (f 0) α β p 2) - f 0) *
      zoom Z (f 0) α β p 1, zoom Z (f 0) α β p 2) = (p 0 + f (p 2) * p 1, p 2) := by
  rw [zoom_apply_two, zoom_proj_fst]
  simp only [unzoom]
  ext
  · simp only
    field_simp
    ring
  · rfl

theorem continuous_unzoom {f : ℝ → ℝ} (hf : Continuous f) (Z α β : ℝ) :
    Continuous (unzoom f Z α β) := by
  unfold unzoom
  fun_prop

/-- The preimage of a planar set under `unzoom` has `Z` times its area. -/
theorem volume_unzoom_preimage {f : ℝ → ℝ} (hf : Continuous f) {Z : ℝ} (hZ : 0 < Z)
    (α β : ℝ) {G : Set (ℝ × ℝ)} (hG : MeasurableSet G) :
    volume (unzoom f Z α β ⁻¹' G) = ENNReal.ofReal Z * volume G := by
  have hm : MeasurableSet (unzoom f Z α β ⁻¹' G) :=
    hG.preimage (continuous_unzoom hf Z α β).measurable
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm, Measure.prod_apply_symm hG,
    ← lintegral_const_mul _ (measurable_measure_prodMk_right hG)]
  refine lintegral_congr fun z => ?_
  have he : (fun u' => (u', z)) ⁻¹' (unzoom f Z α β ⁻¹' G) =
      (fun u' => u' / Z + f z * (α + β * z)) ⁻¹' ((fun u => (u, z)) ⁻¹' G) := by
    ext u'; simp [unzoom]
  rw [he, volume_preimage_affine hZ]

end WangZahlLot.Obl.wz_intermediate_twist_normalization
