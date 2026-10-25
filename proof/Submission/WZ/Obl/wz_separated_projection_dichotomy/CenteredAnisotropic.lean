-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CenteredAnisotropic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CappedAnisotropic
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ZoomClosedFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleMaps

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

noncomputable def cappedAnisotropicCenter (e : Plane) (h c : ℝ) : Plane :=
  if h < 1 then (h⁻¹ * c) • perp e else 0

theorem capped_anisotropic_centered_norm {e b : Plane} {h c : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1) (hb : ‖b‖ ≤ 4)
    (hstrip : h < 1 → |inner ℝ b (perp e) - c| ≤ h) :
    ‖anisotropicMap e 1 h⁻¹ b - cappedAnisotropicCenter e h c‖ ≤ 5 := by
  by_cases hlt : h < 1
  · rw [cappedAnisotropicCenter, if_pos hlt]
    have hform : anisotropicMap e 1 h⁻¹ b - (h⁻¹ * c) • perp e =
        (inner ℝ b e) • e + (h⁻¹ * (inner ℝ b (perp e) - c)) • perp e := by
      simp only [anisotropicMap, one_mul]
      module
    rw [hform]
    have hecoord : |inner ℝ b e| ≤ 4 :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using hb)
    have hpcoord : |h⁻¹ * (inner ℝ b (perp e) - c)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hh)]
      calc h⁻¹ * |inner ℝ b (perp e) - c| ≤ h⁻¹ * h :=
          mul_le_mul_of_nonneg_left (hstrip hlt) (by positivity)
        _ = 1 := inv_mul_cancel₀ hh.ne'
    calc ‖(inner ℝ b e) • e + (h⁻¹ * (inner ℝ b (perp e) - c)) • perp e‖ ≤
          ‖(inner ℝ b e) • e‖ + ‖(h⁻¹ * (inner ℝ b (perp e) - c)) • perp e‖ := norm_add_le _ _
      _ = |inner ℝ b e| + |h⁻¹ * (inner ℝ b (perp e) - c)| := by
        simp only [norm_smul, Real.norm_eq_abs, perp_norm, he, mul_one]
      _ ≤ 5 := by linarith
  · have hh' : h = 1 := le_antisymm hh1 (le_of_not_gt hlt)
    rw [cappedAnisotropicCenter, if_neg hlt, sub_zero, hh', inv_one,
      anisotropicMap_one_one he]
    exact hb.trans (by norm_num : (4 : ℝ) ≤ 5)

theorem half_zoom_norm {x b : Plane} (h : ‖x - b‖ ≤ 5) : ‖zoom b (1 / 2) x‖ ≤ 4 := by
  rw [zoom, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  linarith

theorem half_zoom_separation {b x y : Plane} (h : 1 / 2 ≤ ‖x - y‖) :
    1 / 4 ≤ ‖zoom b (1 / 2) x - zoom b (1 / 2) y‖ := by
  rw [← dist_eq_norm, zoom_dist b (by norm_num), dist_eq_norm]
  linarith

theorem CoverLower.of_half_zoom_triples {δ N : ℝ} {H : Finset Triple} (b : Plane)
    (hδ : 0 ≤ δ)
    (hcov : CoverLower (δ / 2)
      (DotSet (↑(H.image (zoomTriple b (1 / 2) (1 / 2))) : Set Triple)) N) :
    CoverLower δ (DotSet (↑H : Set Triple)) N := by
  classical
  have hc := hcov.affine_image (u := 0) (by norm_num : (0 : ℝ) < 4)
  have hrad : 4 * (δ / 2) = 2 * δ := by ring
  rw [hrad] at hc
  have hs : CoverLower (2 * δ) (DotSet (↑H : Set Triple)) N := by
    apply hc.mono_set
    rintro t ⟨s, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨q, hq, ?_⟩
    change 4 * dotValue (zoomTriple b (1 / 2) (1 / 2) q) + 0 = dotValue q
    rw [dotValue_zoomTriple]
    ring
  exact hs.mono_radius (by linarith)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
