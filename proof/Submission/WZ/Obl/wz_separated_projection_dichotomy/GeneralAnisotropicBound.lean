-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.GeneralAnisotropicBound.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CenteredAnisotropic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem norm_sub_le_of_common_center {x y b : Plane} {R : ℝ}
    (hx : ‖x - b‖ ≤ R) (hy : ‖y - b‖ ≤ R) : ‖x - y‖ ≤ 2 * R := by
  have hid : x - y = (x - b) - (y - b) := by abel
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith)

theorem anisotropic_dot_bound_general {F G U : Finset Plane} {H : Finset Triple}
    {e : Plane} {h c : ℝ} (he : ‖e‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hH : H ⊆ F ×ˢ (G ×ˢ U))
    (hFnorm : ∀ a ∈ F, ‖a‖ ≤ 4) (hGnorm : ∀ b ∈ G, ‖b‖ ≤ 4) (hUnorm : ∀ b ∈ U, ‖b‖ ≤ 4)
    (hFstrip : h < 1 → ∀ a ∈ F, |inner ℝ a e| ≤ h)
    (hGstrip : h < 1 → ∀ b ∈ G, |inner ℝ b (perp e) - c| ≤ h)
    (hUstrip : h < 1 → ∀ b ∈ U, |inner ℝ b (perp e) - c| ≤ h) :
    ∀ s ∈ DotSet (↑H : Set Triple), |s| ≤ 50 * h := by
  rintro s ⟨p, hp, rfl⟩
  have ha := (Finset.mem_product.mp (hH hp)).1
  have hx := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
  have hb := (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).2
  rw [anisotropicMap_dual_dot he hh, abs_mul, abs_of_pos hh]
  have hA := capped_anisotropic_first_norm he hh hh1 (hFnorm p.1 ha) (fun hlt => hFstrip hlt p.1 ha)
  have hX := capped_anisotropic_centered_norm he hh hh1 (hGnorm p.2.1 hx)
    (fun hlt => hGstrip hlt p.2.1 hx)
  have hY := capped_anisotropic_centered_norm he hh hh1 (hUnorm p.2.2 hb)
    (fun hlt => hUstrip hlt p.2.2 hb)
  have hB := norm_sub_le_of_common_center hX hY
  have hi := abs_real_inner_le_norm (anisotropicMap e h⁻¹ 1 p.1)
    (anisotropicMap e 1 h⁻¹ p.2.1 - anisotropicMap e 1 h⁻¹ p.2.2)
  have hprod : ‖anisotropicMap e h⁻¹ 1 p.1‖ *
      ‖anisotropicMap e 1 h⁻¹ p.2.1 - anisotropicMap e 1 h⁻¹ p.2.2‖ ≤ 50 := by
    nlinarith [norm_nonneg (anisotropicMap e h⁻¹ 1 p.1),
      norm_nonneg (anisotropicMap e 1 h⁻¹ p.2.1 - anisotropicMap e 1 h⁻¹ p.2.2)]
  nlinarith

end WangZahlLot.Obl.wz_separated_projection_dichotomy
