-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CoarseNormals.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.UnitTransport
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover
import Submission.WZ.Obl.wz_flat_factored_improvement.Diagonal

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (Space diagonalMap diagonalMap_apply
  diagonalMap_norm_le diagonalMap_norm_lower)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_unit pd inner_coords)

def coarseLinear (θ : ℝ) : Space →ₗ[ℝ] Space := diagonalMap ![θ⁻¹, θ⁻¹, 1]
def dualLinear (θ : ℝ) : Space →ₗ[ℝ] Space := diagonalMap ![θ, θ, 1]

lemma coarse_dual {θ : ℝ} (hθ : 0 < θ) (p : Space) : coarseLinear θ (dualLinear θ p) = p := by
  ext j
  fin_cases j <;> simp [coarseLinear, dualLinear, diagonalMap_apply, hθ.ne']

lemma dual_coarse {θ : ℝ} (hθ : 0 < θ) (p : Space) : dualLinear θ (coarseLinear θ p) = p := by
  ext j
  fin_cases j <;> simp [coarseLinear, dualLinear, diagonalMap_apply, hθ.ne']

lemma dual_inner_coarse {θ : ℝ} (hθ : 0 < θ) (p q : Space) :
    inner ℝ (dualLinear θ p) (coarseLinear θ q) = inner ℝ p q := by
  rw [inner_coords, inner_coords]
  norm_num [coarseLinear, dualLinear, diagonalMap_apply]
  field_simp

lemma coarseLinear_norm_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (p : Space) :
    ‖coarseLinear θ p‖ ≤ θ⁻¹ * ‖p‖ := by
  apply diagonalMap_norm_le (inv_pos.mpr hθ).le
  intro j
  fin_cases j <;> simp [abs_of_pos hθ, abs_of_pos (inv_pos.mpr hθ)]
  exact (one_le_inv₀ hθ).mpr hθ1

lemma dualLinear_norm_lower {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (p : Space) :
    θ * ‖p‖ ≤ ‖dualLinear θ p‖ := by
  apply diagonalMap_norm_lower hθ.le
  intro j
  fin_cases j <;> simp [abs_of_pos hθ, hθ1]

lemma dualLinear_norm_pos {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {p : Space} (hp : p ≠ 0) :
    0 < ‖dualLinear θ p‖ := (mul_pos hθ (norm_pos_iff.mpr hp)).trans_le (dualLinear_norm_lower hθ hθ1 p)

lemma dualLinear_normal_upper {θ C : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    {p : Space} (hp : ‖p‖ = 1) (hp2 : |p 2| ≤ C * θ) :
    ‖dualLinear θ p‖ ≤ (C + 2) * θ := by
  have h0 : |p 0| ≤ 1 := by simpa [hp, Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have h1 : |p 1| ≤ 1 := by simpa [hp, Real.norm_eq_abs] using PiLp.norm_apply_le p 1
  have hh := norm_le_coord_sum (dualLinear θ p)
  norm_num [dualLinear, diagonalMap_apply, abs_mul, abs_of_pos hθ] at hh
  change ‖dualLinear θ p‖ ≤ θ * |p 0| + θ * |p 1| + |p 2| at hh
  nlinarith [mul_le_mul_of_nonneg_left h0 hθ.le, mul_le_mul_of_nonneg_left h1 hθ.le]

lemma coarse_unit_dual {θ : ℝ} (hθ : 0 < θ) (p : Space) :
    coarseLinear θ (unit (dualLinear θ p)) = ‖dualLinear θ p‖⁻¹ • p := by
  rw [unit, map_smul, coarse_dual hθ]

lemma unit_coarse_unit_dual {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {p : Space} (hp : ‖p‖ = 1) :
    unit (coarseLinear θ (unit (dualLinear θ p))) = p := by
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
  rw [coarse_unit_dual hθ, unit_pos_smul (inv_pos.mpr (dualLinear_norm_pos hθ hθ1 hp0))]
  simp [unit, hp]

/-- On normals almost perpendicular to the coarse axis, undoing the
normalized dual map loses only a fixed constant in projective distance. -/
lemma normal_transport_inverse_pd {θ C : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 < C)
    {p q : Space} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpbound : ‖dualLinear θ p‖ ≤ C * θ) :
    pd p q ≤ 2 * C * pd (unit (dualLinear θ p)) (unit (dualLinear θ q)) := by
  have hp0 : p ≠ 0 := by intro hz; simp [hz] at hp
  have hq0 : q ≠ 0 := by intro hz; simp [hz] at hq
  have hDp := dualLinear_norm_pos hθ hθ1 hp0
  have hDq := dualLinear_norm_pos hθ hθ1 hq0
  have hnorm (v : Space) (hv : ‖v‖ = 1) (hDv : 0 < ‖dualLinear θ v‖) :
      ‖coarseLinear θ (unit (dualLinear θ v))‖ = ‖dualLinear θ v‖⁻¹ := by
    rw [coarse_unit_dual hθ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hDv), hv, mul_one]
  have hlower : (C * θ)⁻¹ ≤ ‖coarseLinear θ (unit (dualLinear θ p))‖ := by
    rw [hnorm p hp hDp]
    exact inv_anti₀ hDp hpbound
  have hnonzero : coarseLinear θ (unit (dualLinear θ q)) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnorm q hq hDq]
    exact (inv_pos.mpr hDq).ne'
  have hh := unit_linear_pd_le (coarseLinear θ) (inv_pos.mpr hθ).le
    (inv_pos.mpr (mul_pos hC hθ)) (coarseLinear_norm_le hθ hθ1) hlower hnonzero
  rw [unit_coarse_unit_dual hθ hθ1 hp, unit_coarse_unit_dual hθ hθ1 hq] at hh
  have he : 2 * θ⁻¹ / (C * θ)⁻¹ = 2 * C := by field_simp
  rwa [he] at hh

lemma normal_transport_coordinate {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    {n : Space} (hn : n ≠ 0) (p : Space) :
    inner ℝ n p = ‖dualLinear θ n‖ * inner ℝ (unit (dualLinear θ n)) (coarseLinear θ p) := by
  have hn0 := dualLinear_norm_pos hθ hθ1 hn
  rw [unit, real_inner_smul_left, dual_inner_coarse hθ]
  field_simp

lemma normal_transport_orthogonal {θ : ℝ} (hθ : 0 < θ) {n l : Space}
    (hnl : inner ℝ n l = 0) :
    inner ℝ (unit (dualLinear θ n)) (unit (coarseLinear θ l)) = 0 := by
  rw [unit, unit, real_inner_smul_left, inner_smul_right, dual_inner_coarse hθ, hnl]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
