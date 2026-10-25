-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSRescale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSGeometry
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

/-!
# Anisotropic rescaling of a fibre

`aniso w0 a` dilates by `a` transversally to the unit vector `w0` and fixes `w0`.
The rescaling `p ↦ b • aniso w0 a (p - c0)` maps a unit `δ`-tube nearly parallel
to `w0` into a unit tube of radius `b a δ` (after extending the shorter image of the
axis to unit length), changes volumes by `b ^ 3 a ^ 2`, and expands distances by at
most `a`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace Pointwise
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate)

/-- Dilation by `a` transverse to `w0`. -/
noncomputable def aniso (w0 : Space) (a : ℝ) : Space →L[ℝ] Space :=
  a • ContinuousLinearMap.id ℝ Space + (1 - a) • (innerSL ℝ w0).smulRight w0

theorem aniso_apply (w0 : Space) (a : ℝ) (p : Space) :
    aniso w0 a p = a • p + (1 - a) • (⟪w0, p⟫ • w0) := by
  simp [aniso]

theorem aniso_self {w0 : Space} (hw0 : ‖w0‖ = 1) (a : ℝ) : aniso w0 a w0 = w0 := by
  rw [aniso_apply, real_inner_self_eq_norm_sq, hw0]
  module

/-- Squared norm of the anisotropic image. -/
theorem norm_aniso_sq {w0 : Space} (hw0 : ‖w0‖ = 1) (a : ℝ) (p : Space) :
    ‖aniso w0 a p‖ ^ 2 = a ^ 2 * ‖p‖ ^ 2 + (1 - a ^ 2) * ⟪w0, p⟫ ^ 2 := by
  rw [aniso_apply, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq p]
  have hww : ⟪w0, w0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw0]; norm_num
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [hww, real_inner_comm p w0]
  ring

theorem inner_sq_le_norm_sq {w0 : Space} (hw0 : ‖w0‖ = 1) (p : Space) :
    ⟪w0, p⟫ ^ 2 ≤ ‖p‖ ^ 2 := by
  have h := abs_real_inner_le_norm w0 p
  rw [hw0, one_mul] at h
  calc ⟪w0, p⟫ ^ 2 = |⟪w0, p⟫| ^ 2 := (sq_abs _).symm
    _ ≤ ‖p‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2

theorem norm_aniso_le {w0 : Space} (hw0 : ‖w0‖ = 1) {a : ℝ} (ha : 1 ≤ a) (p : Space) :
    ‖aniso w0 a p‖ ≤ a * ‖p‖ := by
  have h := norm_aniso_sq hw0 a p
  have hi := inner_sq_le_norm_sq hw0 p
  have hsq : ‖aniso w0 a p‖ ^ 2 ≤ (a * ‖p‖) ^ 2 := by
    rw [h, mul_pow]
    have : (1 - a ^ 2) * ⟪w0, p⟫ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem norm_le_norm_aniso {w0 : Space} (hw0 : ‖w0‖ = 1) {a : ℝ} (ha : 1 ≤ a) (p : Space) :
    ‖p‖ ≤ ‖aniso w0 a p‖ := by
  have h := norm_aniso_sq hw0 a p
  have hi := inner_sq_le_norm_sq hw0 p
  have hsq : ‖p‖ ^ 2 ≤ ‖aniso w0 a p‖ ^ 2 := by
    rw [h]
    have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg ha2 (sub_nonneg.mpr hi)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- The image of a unit vector close to `w0` has norm at most `1 + a² θ² / 2`. -/
theorem norm_aniso_unit_le {w0 v : Space} (hw0 : ‖w0‖ = 1) (hv : ‖v‖ = 1) {a θ : ℝ}
    (ha : 1 ≤ a) (hvw : ‖v - w0‖ ≤ θ) : ‖aniso w0 a v‖ ≤ 1 + a ^ 2 * θ ^ 2 := by
  have h := norm_aniso_sq hw0 a v
  rw [hv] at h
  -- the transverse part has norm at most `θ`
  have hperp : 1 - ⟪w0, v⟫ ^ 2 ≤ θ ^ 2 := by
    have h1 : ‖v - w0‖ ^ 2 = 2 - 2 * ⟪w0, v⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
      have hww : ⟪w0, w0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw0]; norm_num
      simp only [inner_sub_left, inner_sub_right]
      rw [hvv, hww, real_inner_comm v w0]
      ring
    have h2 : ⟪w0, v⟫ ≤ 1 := by
      have := real_inner_le_norm w0 v; rw [hw0, hv] at this; linarith
    have h5 : -1 ≤ ⟪w0, v⟫ := by
      have := neg_le_of_abs_le (abs_real_inner_le_norm w0 v); rw [hw0, hv] at this; linarith
    have h4 : ‖v - w0‖ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvw 2
    have h6 : 1 - ⟪w0, v⟫ ^ 2 ≤ 2 - 2 * ⟪w0, v⟫ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h2)]
    linarith
  have hsq : ‖aniso w0 a v‖ ^ 2 ≤ (1 + a ^ 2 * θ ^ 2) ^ 2 := by
    rw [h]
    have hθ2 : 0 ≤ a ^ 2 * θ ^ 2 := by positivity
    have hq0 : 0 ≤ 1 - ⟪w0, v⟫ ^ 2 := by
      have := inner_sq_le_norm_sq hw0 v; rw [hv] at this; linarith
    have e1 : a ^ 2 * 1 ^ 2 + (1 - a ^ 2) * ⟪w0, v⟫ ^ 2 =
        1 - (1 - ⟪w0, v⟫ ^ 2) + a ^ 2 * (1 - ⟪w0, v⟫ ^ 2) := by ring
    have e2 : a ^ 2 * (1 - ⟪w0, v⟫ ^ 2) ≤ a ^ 2 * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hperp (sq_nonneg a)
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The determinant of the anisotropic dilation is `a²`. -/
theorem det_aniso {w0 : Space} (hw0 : ‖w0‖ = 1) (a : ℝ) :
    LinearMap.det (aniso w0 a : Space →ₗ[ℝ] Space) = a ^ 2 := by
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hw0
  rw [← LinearMap.det_toMatrix b.toBasis]
  have hb0 : ∀ i : Fin 3, ⟪w0, b i⟫ = if i = 0 then 1 else 0 := by
    intro i
    rw [← hb]
    have := orthonormal_iff_ite.mp b.orthonormal 0 i
    rw [this]
    by_cases h : i = 0
    · simp [h]
    · simp [h, Ne.symm h]
  have hcol : ∀ i j : Fin 3, LinearMap.toMatrix b.toBasis b.toBasis
      (aniso w0 a : Space →ₗ[ℝ] Space) i j =
      if i = j then (if j = 0 then 1 else a) else 0 := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    rw [aniso_apply, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hb0 j, orthonormal_iff_ite.mp b.orthonormal i j]
    have hbi : ⟪b i, w0⟫ = if i = 0 then 1 else 0 := by rw [real_inner_comm]; exact hb0 i
    rw [hbi]
    by_cases hij : i = j
    · subst hij; by_cases h0 : i = 0 <;> simp [h0]
    · by_cases hj0 : j = 0
      · subst hj0; simp [hij]
      · simp [hij, hj0]
  rw [Matrix.det_fin_three]
  simp only [hcol]
  simp
  ring

/-- Volumes scale by `a²` under the anisotropic dilation. -/
theorem volume_image_aniso {w0 : Space} (hw0 : ‖w0‖ = 1) {a : ℝ} (s : Set Space) :
    volume (aniso w0 a '' s) = ENNReal.ofReal (a ^ 2) * volume s := by
  have h := MeasureTheory.Measure.addHaar_image_linearMap volume
    (aniso w0 a : Space →ₗ[ℝ] Space) s
  rw [det_aniso hw0, abs_of_nonneg (sq_nonneg a)] at h
  simpa using h

/-- The rescaling map of a fibre. -/
noncomputable def resc (w0 c0 : Space) (a b : ℝ) (p : Space) : Space :=
  b • aniso w0 a (p - c0)

theorem resc_sub (w0 c0 : Space) (a b : ℝ) (p q : Space) :
    resc w0 c0 a b p - resc w0 c0 a b q = b • aniso w0 a (p - q) := by
  simp only [resc, ← smul_sub, ← map_sub]
  congr 2
  abel

theorem norm_resc_sub_le {w0 c0 : Space} (hw0 : ‖w0‖ = 1) {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b)
    (p q : Space) : ‖resc w0 c0 a b p - resc w0 c0 a b q‖ ≤ b * a * ‖p - q‖ := by
  rw [resc_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_aniso_le hw0 ha _) hb

/-- Volumes scale by `b³ a²` under the rescaling. -/
theorem volume_image_resc {w0 c0 : Space} (hw0 : ‖w0‖ = 1) {a b : ℝ} (hb : 0 ≤ b)
    (s : Set Space) :
    volume (resc w0 c0 a b '' s) = ENNReal.ofReal (b ^ 3 * a ^ 2) * volume s := by
  have he : resc w0 c0 a b '' s = b • (aniso w0 a '' ((fun p => p - c0) '' s)) := by
    ext q
    simp only [mem_image, Set.mem_smul_set, resc]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨aniso w0 a (p - c0), ⟨p - c0, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨y', ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  rw [he, Measure.addHaar_smul, finrank_euclideanSpace_fin, volume_image_aniso hw0]
  have ht : (fun p : Space => p - c0) '' s = (fun p => -c0 + p) '' s := by
    ext q; simp [sub_eq_neg_add]
  rw [ht, image_add_left, measure_preimage_add, abs_of_nonneg (pow_nonneg hb 3),
    ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hb 3)]

/-- A unit tube nearly parallel to `w0` maps into a unit tube of radius `b a δ`. -/
theorem resc_tube_subset {w0 c0 x v : Space} (hw0 : ‖w0‖ = 1) {a b δ : ℝ} (ha : 1 ≤ a)
    (hb : 0 < b) (hbL : b * ‖aniso w0 a v‖ ≤ 1) (hL : 0 < ‖aniso w0 a v‖) :
    resc w0 c0 a b '' Tube δ x v ⊆
      Tube (b * a * δ) (resc w0 c0 a b x) (‖aniso w0 a v‖⁻¹ • aniso w0 a v) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp
  apply mem_Tube_of_param (t := b * t * ‖aniso w0 a v‖)
  · constructor
    · have := ht.1; positivity
    · calc b * t * ‖aniso w0 a v‖ = t * (b * ‖aniso w0 a v‖) := by ring
        _ ≤ 1 * 1 := mul_le_mul ht.2 hbL (by positivity) zero_le_one
        _ = 1 := one_mul 1
  · have he : resc w0 c0 a b p - (resc w0 c0 a b x +
        (b * t * ‖aniso w0 a v‖) • (‖aniso w0 a v‖⁻¹ • aniso w0 a v)) =
        resc w0 c0 a b p - resc w0 c0 a b (x + t • v) := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hL.ne', mul_one]
      congr 1
      simp only [resc, map_add, map_smul, add_sub_right_comm, smul_add, smul_smul]
    rw [he]
    calc ‖resc w0 c0 a b p - resc w0 c0 a b (x + t • v)‖ ≤ b * a * ‖p - (x + t • v)‖ :=
          norm_resc_sub_le hw0 ha hb.le _ _
      _ < b * a * δ := mul_lt_mul_of_pos_left hpt (by positivity)

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
