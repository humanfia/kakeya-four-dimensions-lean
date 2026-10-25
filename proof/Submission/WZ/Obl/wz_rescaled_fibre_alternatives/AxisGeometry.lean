-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.AxisGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Normalization
import Submission.WZ.Obl.wz_tower_convex_count_composition

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate
  (axis norm_axis stretch affine_sub norm_sq_coords norm_le_stretch)

lemma centered_segment (x v : Space) {a : ℝ} (ha : |a| ≤ 1 / 2) :
    x + (1 / 2 : ℝ) • v + a • v ∈ segment ℝ x (x + v) := by
  rw [segment_eq_image']
  refine ⟨a + 1 / 2, ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩, ?_⟩
  simp only [add_sub_cancel_left]
  module

lemma centered_doubled_segment (x v : Space) {a : ℝ} (ha : |a| ≤ 1) :
    x + (1 / 2 : ℝ) • v + a • v ∈ segment ℝ (x - (1 / 2 : ℝ) • v)
      (x - (1 / 2 : ℝ) • v + 2 • v) := by
  rw [segment_eq_image']
  refine ⟨(a + 1) / 2, ⟨by linarith [(abs_le.mp ha).1], by linarith [(abs_le.mp ha).2]⟩, ?_⟩
  simp only [add_sub_cancel_left]
  module

lemma tube_dist_midpoint {s : ℝ} {x v p : Space} (hv : ‖v‖ = 1)
    (hp : p ∈ tube s x v) : dist p (x + (1 / 2 : ℝ) • v) < s + 1 / 2 := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have hq : dist (x + a • v) (x + (1 / 2 : ℝ) • v) ≤ 1 / 2 := by
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, hv, mul_one]
    exact abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  exact (dist_triangle _ _ _).trans_lt (add_lt_add_of_lt_of_le hpq hq)

lemma parent_axis_close {r s : ℝ} (hs : 0 < s) {x v y w : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : tube s x v ⊆ tube r y w) :
    ∃ b : ℝ, |b| = 1 ∧ ‖w - b • v‖ < 6 * r := by
  have h0 := hT (self_subset_thickening hs _ (left_mem_segment ℝ x (x + v)))
  have h1 := hT (self_subset_thickening hs _ (right_mem_segment ℝ x (x + v)))
  rcases WangZahlLot.Obl.wz_tower_convex_count_composition.parent_endpoints hv hw h0 h1 with h | h
  · refine ⟨1, by norm_num, ?_⟩
    rw [one_smul]
    have he : w - v = (y + w - (x + v)) - (y - x) := by abel
    rw [he]
    have hh := norm_sub_le (y + w - (x + v)) (y - x)
    simp only [dist_eq_norm] at h
    linarith [h.1, h.2]
  · refine ⟨-1, by norm_num, ?_⟩
    rw [neg_one_smul]
    have he : w - -v = (y + w - x) - (y - (x + v)) := by abel
    rw [he]
    have hh := norm_sub_le (y + w - x) (y - (x + v))
    simp only [dist_eq_norm] at h
    linarith [h.1, h.2]

lemma transverse_coord_norm_le (z : Space) : ‖z - (z 0) • axis‖ ≤ ‖z‖ := by
  have he : ‖z - (z 0) • axis‖ ^ 2 = z 1 ^ 2 + z 2 ^ 2 := by
    rw [norm_sq_coords]
    simp [axis, PiLp.sub_apply, PiLp.smul_apply]
  have hz := norm_sq_coords z
  nlinarith [sq_nonneg (z 0), norm_nonneg z, norm_nonneg (z - (z 0) • axis)]

lemma stretch_decompose (r : ℝ) (z : Space) :
    stretch r z = (z 0) • axis + r • (z - (z 0) • axis) := by
  ext i
  fin_cases i <;> simp [stretch, axis] <;> ring

lemma normalize_inverse_difference (e : Space ≃ₗᵢ[ℝ] Space) {y w : Space}
    (hew : e w = axis) {r : ℝ} (hr : 0 < r) (p q : Space) :
    p - q = contraction⁻¹ • e.symm (stretch r (normalize e y w r hr p - normalize e y w r hr q)) := by
  rw [normalize, affine_sub, map_smul, map_smul, smul_smul]
  have he : stretch r (stretch r⁻¹ (e (p - q))) = e (p - q) := by
    ext i
    fin_cases i <;> simp [stretch, hr.ne']
  rw [he, e.symm_apply_apply]
  norm_num

lemma normalize_inverse_norm (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (p q : Space) :
    ‖p - q‖ ≤ ‖normalize e y w r hr p - normalize e y w r hr q‖ / contraction := by
  have h := norm_le_stretch ((one_le_inv₀ hr).mpr hr1) (e (p - q))
  rw [e.norm_map] at h
  rw [normalize, affine_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : 0 < contraction)]
  convert h using 1 <;> norm_num [contraction, div_eq_mul_inv] <;> ring

/-- The inverse map has small transverse displacement relative to every child axis. -/
lemma normalize_inverse_axis (e : Space ≃ₗᵢ[ℝ] Space) {y w x v : Space}
    (hew : e w = axis) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hT : tube s x v ⊆ tube r y w)
    (p q : Space) :
    ∃ a : ℝ, |a| ≤ ‖normalize e y w r hr p - normalize e y w r hr q‖ / contraction ∧
      ‖p - q - a • v‖ ≤ (7 * r / contraction) *
        ‖normalize e y w r hr p - normalize e y w r hr q‖ := by
  obtain ⟨b, hb, hclose⟩ := parent_axis_close hs hv hw hT
  let z := normalize e y w r hr p - normalize e y w r hr q
  have h0 : |z 0| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z 0
  have hew' : e.symm axis = w := by rw [← hew, e.symm_apply_apply]
  have he : p - q = (contraction⁻¹ * z 0) • w +
      (contraction⁻¹ * r) • e.symm (z - (z 0) • axis) := by
    rw [normalize_inverse_difference e hew hr p q]
    change contraction⁻¹ • e.symm (stretch r z) = _
    rw [stretch_decompose, map_add, map_smul, map_smul, hew', smul_add, smul_smul, smul_smul]
  refine ⟨contraction⁻¹ * z 0 * b, ?_, ?_⟩
  · rw [abs_mul, abs_mul, hb, mul_one, abs_of_pos (by norm_num : 0 < contraction⁻¹)]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left h0 (by norm_num : 0 ≤ contraction⁻¹)
  · rw [he]
    have hvec : (contraction⁻¹ * z 0) • w +
        (contraction⁻¹ * r) • e.symm (z - (z 0) • axis) -
        (contraction⁻¹ * z 0 * b) • v =
      (contraction⁻¹ * z 0) • (w - b • v) +
        (contraction⁻¹ * r) • e.symm (z - (z 0) • axis) := by module
    rw [hvec]
    calc
      _ ≤ ‖(contraction⁻¹ * z 0) • (w - b • v)‖ +
          ‖(contraction⁻¹ * r) • e.symm (z - (z 0) • axis)‖ := norm_add_le _ _
      _ = (contraction⁻¹ * |z 0|) * ‖w - b • v‖ +
          (contraction⁻¹ * r) * ‖z - (z 0) • axis‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_mul, abs_of_pos (by norm_num : 0 < contraction⁻¹),
          abs_of_pos (by positivity : 0 < contraction⁻¹ * r), e.symm.norm_map]
      _ ≤ (contraction⁻¹ * ‖z‖) * (6 * r) + (contraction⁻¹ * r) * ‖z‖ := by
        exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left h0 (by norm_num))
          hclose.le (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (transverse_coord_norm_le z) (by positivity))
      _ = _ := by dsimp [z]; ring

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
