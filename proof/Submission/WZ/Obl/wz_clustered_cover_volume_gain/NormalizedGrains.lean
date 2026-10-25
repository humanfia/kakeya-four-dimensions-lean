-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NormalizedGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CoarseAffine

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit)
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (prism)

lemma coarse_prism_sizes {θ ρ a c r : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ)
    (hρθ : ρ ≤ θ) (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c) (hr : 0 < r)
    (hrc : r * c = 1 / 100000000) :
    0 < r * a / (2 * θ) ∧ r * a / (2 * θ) ≤ r * ρ * c / θ ∧
      r * ρ * c / θ ≤ 1 / 1000000 := by
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity : 0 < 2 * θ) hθ).mpr
    have hh := mul_le_mul_of_nonneg_left (show a ≤ 2 * (ρ * c) by linarith [mul_pos hρ hc])
      (mul_pos hr hθ).le
    convert hh using 1 <;> ring
  · apply (div_le_iff₀ hθ).mpr
    calc
      r * ρ * c = ρ * (r * c) := by ring
      _ = ρ / 100000000 := by rw [hrc]; ring
      _ ≤ θ / 100000000 := div_le_div_of_nonneg_right hρθ (by norm_num)
      _ ≤ (1 / 1000000 : ℝ) * θ := by linarith

/-- One common affine map encloses all grains by prisms with the fixed long
side used in the transverse filling estimates. -/
theorem coarse_grain_prism {θ ρ a c r : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hρ : 0 < ρ) (hρθ : ρ ≤ θ)
    (ha : 0 < a) (hac : a ≤ ρ * c) (hc : 0 < c) (hr : 0 < r)
    (hrc : r * c = 1 / 100000000) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (haxis : ‖coarseLinear θ (boxAxis e 2)‖ ≤ 43) :
    ∃ u : OrthonormalBasis (Fin 3) ℝ V,
      u 0 = unit (dualLinear θ (boxAxis e 0)) ∧
      coarseAffine hθ hr '' P a (ρ * c) c z e ⊆
        prism (r * a / (2 * θ)) (r * ρ * c / θ) (coarseAffine hθ hr z) u := by
  obtain ⟨u, hu0, hu2, hbox⟩ := coarse_prism_enclosure hθ hθ1 (by positivity : 0 ≤ a / 2)
    (show a / 2 ≤ (ρ * c) / 2 by linarith)
    (show (ρ * c) / 2 ≤ θ * (c / 2) by nlinarith [mul_le_mul_of_nonneg_right hρθ hc.le])
    (by positivity : 0 ≤ c / 2) (by norm_num : (0 : ℝ) ≤ 43) (frozenBasis e) z haxis
  refine ⟨u, hu0, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hU := hbox ⟨p, by rwa [← frozen_prism_box], rfl⟩
  have hcoord (j : Fin 3) :
      |inner ℝ (u j) (coarseAffine hθ hr p - coarseAffine hθ hr z)| =
        r * |inner ℝ (u j) (coarseLinear θ p - coarseLinear θ z)| := by
    rw [coarseAffine_apply, coarseAffine_apply, ← smul_sub, inner_smul_right, abs_mul, abs_of_pos hr]
  change _ ≤ r * a / (2 * θ) ∧ _ ≤ r * ρ * c / θ ∧ _ ≤ (1 / 1000 : ℝ)
  rw [hcoord 0, hcoord 1, hcoord 2]
  refine ⟨?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left (hU 0) hr.le
    convert hh using 1 <;> dsimp <;> ring
  · have hh := mul_le_mul_of_nonneg_left (hU 1) hr.le
    convert hh using 1 <;> dsimp <;> ring
  · have hh := mul_le_mul_of_nonneg_left (hU 2) hr.le
    change r * |inner ℝ (u 2) (coarseLinear θ p - coarseLinear θ z)| ≤ r * ((43 + 2) * (c / 2)) at hh
    nlinarith

lemma coarse_prism_volume_ratio {θ ρ a c r : ℝ}
    (hθ : 0 < θ) (hρ : 0 < ρ) (ha : 0 < a) (hc : 0 < c) (hr : 0 < r)
    (hrc : r * c = 1 / 100000000) (z : V) (e : V ≃ₗᵢ[ℝ] V)
    (u : OrthonormalBasis (Fin 3) ℝ V) :
    volume (prism (r * a / (2 * θ)) (r * ρ * c / θ) (coarseAffine hθ hr z) u) =
      ENNReal.ofReal 400000 * volume (coarseAffine hθ hr '' P a (ρ * c) c z e) := by
  rw [WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_prism (by positivity) (by positivity)
    _ u.orthonormal, coarseAffine_volume, frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3 / θ ^ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 400000)]
  congr 1
  have he : r = (1 / 100000000 : ℝ) / c := (eq_div_iff hc.ne').mpr hrc
  rw [he]
  field_simp
  <;> ring

lemma coarse_prism_threshold {θ ρ a c r s : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    (h : a ≤ s * ρ * c) (ha : 0 ≤ a) :
    r * a / (2 * θ) ≤ s * (r * ρ * c / θ) := by
  have hh := mul_le_mul_of_nonneg_left (show a ≤ 2 * (s * ρ * c) by linarith) hr.le
  apply (div_le_iff₀ (by positivity : 0 < 2 * θ)).mpr
  convert hh using 1 <;> field_simp <;> ring

lemma coarse_radius_fits {θ ρ c r R t : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    (hR : R ≤ t * ρ * c) : (r / θ) * R ≤ t * (r * ρ * c / θ) := by
  have hh := mul_le_mul_of_nonneg_left hR (div_pos hr hθ).le
  convert hh using 1 <;> ring

lemma coarse_prism_ratio {θ ρ a c r : ℝ} (hθ : θ ≠ 0) (hr : r ≠ 0) (ha : a ≠ 0) :
    (r * ρ * c / θ) / (r * a / (2 * θ)) = 2 * ρ * c / a := by
  field_simp

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
