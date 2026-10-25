-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CappedAnisotropic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AnisotropicLineCount
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AnisotropicStrips

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem anisotropicMap_one_one {e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    anisotropicMap e 1 1 x = x := by
  simpa only [anisotropicMap, one_mul] using unit_inner_decomposition he x

/-- The strip hypothesis is needed only when the map expands. This permits
capping the normalization width at one. -/
theorem capped_anisotropic_line_count {I : Type*} [Fintype I] {f : I → Plane}
    {δ C K ζ h q c : ℝ} {e : Plane}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hK : 1 ≤ K) (hζ : 0 ≤ ζ)
    (hδh : δ ≤ h) (hh1 : h ≤ 1) (hδq : δ ≤ q) (hq : q ≤ 1 / 2)
    (he : ‖e‖ = 1) (hF : IndexedFrostman δ C f)
    (hstrip : h < 1 → ∀ i, |inner ℝ (f i) (perp e) - c| ≤ h)
    (hsmall : 10 * C * q ≤ δ ^ ζ)
    (hline : ∀ (u : Plane) (d s : ℝ), ‖u‖ = 1 → δ ≤ s →
      ((Finset.univ.filter (fun i => |inner ℝ (f i) u - d| < s)).card : ℝ) ≤
        K * (s / h) ^ ζ * (Fintype.card I : ℝ)) :
    ∀ (n : Plane) (d r : ℝ), ‖n‖ = 1 → δ / h ≤ r →
      ((Finset.univ.filter (fun i => |inner ℝ (anisotropicMap e 1 h⁻¹ (f i)) n - d| < r)).card : ℝ) ≤
        K * (r / q) ^ ζ * (Fintype.card I : ℝ) := by
  by_cases hh : h < 1
  · exact anisotropic_line_count hδ hC hK hζ hδh hh1 hδq hq he hF (hstrip hh) hsmall hline
  have hh : h = 1 := le_antisymm hh1 (le_of_not_gt hh)
  intro n d r hn hδr
  have hδr' : δ ≤ r := by simpa only [hh, div_one] using hδr
  have hr : 0 ≤ r := hδ.le.trans hδr'
  have hqp : 0 < q := hδ.trans_le hδq
  have hc := hline n d r hn hδr'
  simp only [hh, div_one] at hc
  simp only [hh, inv_one, anisotropicMap_one_one he]
  apply hc.trans
  have hratio : r ≤ r / q := (le_div_iff₀ hqp).mpr (by nlinarith)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hratio hζ) (zero_le_one.trans hK)

theorem capped_anisotropic_first_norm {e a : Plane} {h : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1) (ha : ‖a‖ ≤ 4)
    (hstrip : h < 1 → |inner ℝ a e| ≤ h) : ‖anisotropicMap e h⁻¹ 1 a‖ ≤ 5 := by
  by_cases hlt : h < 1
  · exact anisotropic_orthogonal_norm he hh (hstrip hlt) ha
  · have hh' : h = 1 := le_antisymm hh1 (le_of_not_gt hlt)
    simpa only [hh', inv_one, anisotropicMap_one_one he] using ha.trans (by norm_num : (4 : ℝ) ≤ 5)

theorem capped_anisotropic_difference_norm {e b x : Plane} {h c : ℝ}
    (he : ‖e‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1) (hbx : ‖b - x‖ ≤ 3)
    (hb : h < 1 → |inner ℝ b (perp e) - c| ≤ h)
    (hx : h < 1 → |inner ℝ x (perp e) - c| ≤ h) :
    ‖anisotropicMap e 1 h⁻¹ b - anisotropicMap e 1 h⁻¹ x‖ ≤ 5 := by
  by_cases hlt : h < 1
  · rw [← anisotropicMap_sub]
    have hperp := strip_difference_perp (hb hlt) (hx hlt)
    have halong : |inner ℝ (b - x) e| ≤ 3 :=
      (abs_real_inner_le_norm _ _).trans (by simpa only [he, mul_one] using hbx)
    have hnorm := anisotropicMap_norm_upper he 1 h⁻¹ (b - x)
    rw [one_mul, abs_mul, abs_of_pos (inv_pos.mpr hh)] at hnorm
    have hhperp : h⁻¹ * |inner ℝ (b - x) (perp e)| ≤ 2 := by
      calc h⁻¹ * |inner ℝ (b - x) (perp e)| ≤ h⁻¹ * (2 * h) := mul_le_mul_of_nonneg_left hperp (by positivity)
        _ = 2 := by field_simp
    linarith
  · have hh' : h = 1 := le_antisymm hh1 (le_of_not_gt hlt)
    simpa only [hh', inv_one, anisotropicMap_one_one he] using hbx.trans (by norm_num : (3 : ℝ) ≤ 5)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
