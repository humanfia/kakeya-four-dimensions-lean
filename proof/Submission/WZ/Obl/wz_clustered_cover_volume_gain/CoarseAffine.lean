-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.CoarseAffine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseNormals
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement

def coarseScales (θ r : ℝ) : Fin 3 → ℝ := ![r / θ, r / θ, r]

lemma coarseScales_pos {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) (j : Fin 3) :
    0 < coarseScales θ r j := by fin_cases j <;> dsimp [coarseScales] <;> positivity

def coarseAffine {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) : V ≃ᵃ[ℝ] V :=
  coordinateAffine (AffineIsometryEquiv.refl ℝ V) (coarseScales θ r)
    (fun j => (coarseScales_pos hθ hr j).ne')

lemma coarseAffine_apply {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) (p : V) :
    coarseAffine hθ hr p = r • coarseLinear θ p := by
  change diagonalMap (coarseScales θ r) p = r • coarseLinear θ p
  ext j
  fin_cases j <;>
    simp [coarseAffine, coordinateAffine_apply, coarseScales, coarseLinear, diagonalMap_apply,
      PiLp.smul_apply, div_eq_mul_inv] <;> ring

lemma coarseAffine_volume {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r) (Q : Set V) :
    volume (coarseAffine hθ hr '' Q) = ENNReal.ofReal (r ^ 3 / θ ^ 2) * volume Q := by
  have hh := coordinateAffine_volume (AffineIsometryEquiv.refl ℝ V) (coarseScales θ r)
    (coarseScales_pos hθ hr) Q
  change volume (coarseAffine hθ hr '' Q) = _ at hh
  rw [hh]
  congr 2
  simp [coarseScales, Fin.prod_univ_three]
  ring

lemma coarseAffine_dist_upper {θ r : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 < r)
    (p q : V) : dist (coarseAffine hθ hr p) (coarseAffine hθ hr q) ≤ (r / θ) * dist p q := by
  rw [dist_eq_norm, coarseAffine_apply, coarseAffine_apply, ← smul_sub, ← map_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hh := mul_le_mul_of_nonneg_left (coarseLinear_norm_le hθ hθ1 (p - q)) hr.le
  simpa only [dist_eq_norm, div_eq_mul_inv, mul_assoc] using hh

lemma inverse_affine_volume {J : ℝ} (hJ : 0 < J) (f : V ≃ᵃ[ℝ] V)
    (hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q) (Q : Set V) :
    volume (f.symm '' Q) = ENNReal.ofReal J⁻¹ * volume Q := by
  have hh : volume Q = ENNReal.ofReal J * volume (f.symm '' Q) := by
    rw [← hvol]
    simp only [Set.image_image, f.apply_symm_apply, Set.image_id']
  have hm := congrArg (fun t : ℝ≥0∞ => (ENNReal.ofReal J)⁻¹ * t) hh
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hJ).ne' ENNReal.ofReal_ne_top,
    one_mul] at hm
  rw [ENNReal.ofReal_inv_of_pos hJ]
  exact hm.symm

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
