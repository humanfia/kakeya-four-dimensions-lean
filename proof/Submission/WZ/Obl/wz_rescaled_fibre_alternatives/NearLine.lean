-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.NearLine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.AxisGeometry

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

/-- Points of a doubled tube lie close to the line through any sufficiently
separated pair of points in the undoubled tube. -/
lemma doubled_near_line {k ρ : ℝ} (hk : 0 < k) (hk1 : k ≤ 1)
    (hρ : 0 < ρ) (hρk : ρ ≤ k / 4) {q₀ q₁ z u q : Space}
    (hu : ‖u‖ = 1) (h₀ : q₀ ∈ tube ρ z u) (h₁ : q₁ ∈ tube ρ z u)
    (hlen : k ≤ ‖q₁ - q₀‖) (hq : q ∈ doubled ρ z u) :
    ∃ a : ℝ, |a| ≤ 4 / k ∧
      ‖q - (1 / 2 : ℝ) • (q₀ + q₁) - a • (q₁ - q₀)‖ ≤ 11 * ρ / k := by
  obtain ⟨p₀, hp₀, hd₀⟩ := mem_thickening_iff.mp h₀
  obtain ⟨p₁, hp₁, hd₁⟩ := mem_thickening_iff.mp h₁
  obtain ⟨p, hp, hd⟩ := mem_thickening_iff.mp hq
  rw [segment_eq_image'] at hp₀ hp₁ hp
  obtain ⟨t₀, ht₀, rfl⟩ := hp₀
  obtain ⟨t₁, ht₁, rfl⟩ := hp₁
  obtain ⟨t, ht, rfl⟩ := hp
  simp only [add_sub_cancel_left, dist_eq_norm] at hd₀ hd₁ hd
  let e₀ := q₀ - (z + t₀ • u)
  let e₁ := q₁ - (z + t₁ • u)
  let E := q - (z - (1 / 2 : ℝ) • u + t • (2 • u))
  have he₀ : ‖e₀‖ < ρ := hd₀
  have he₁ : ‖e₁‖ < ρ := hd₁
  have he : ‖E‖ < 2 * ρ := hd
  have he10 : ‖e₁ - e₀‖ < 2 * ρ :=
    (norm_sub_le _ _).trans_lt (by linarith)
  have headd : ‖(1 / 2 : ℝ) • (e₀ + e₁)‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith [norm_add_le e₀ e₁]
  have hvec : q₁ - q₀ = (t₁ - t₀) • u + (e₁ - e₀) := by dsimp [e₀, e₁]; module
  have hlen' : k ≤ |t₁ - t₀| + 2 * ρ := by
    have hn := norm_add_le ((t₁ - t₀) • u) (e₁ - e₀)
    rw [← hvec, norm_smul, Real.norm_eq_abs, hu, mul_one] at hn
    linarith
  have ht10 : k / 2 ≤ |t₁ - t₀| := by linarith
  have htne : t₁ - t₀ ≠ 0 := by intro h; rw [h, abs_zero] at ht10; linarith
  let c := 2 * t - 1 / 2 - (t₀ + t₁) / 2
  have hc : |c| ≤ 2 := abs_le.mpr ⟨by dsimp [c]; linarith [ht.1, ht₀.2, ht₁.2],
    by dsimp [c]; linarith [ht.2, ht₀.1, ht₁.1]⟩
  let a := c / (t₁ - t₀)
  have ha : |a| ≤ 4 / k := by
    dsimp [a]
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr htne)).mpr
    calc
      |c| ≤ 2 := hc
      _ ≤ 4 / k * |t₁ - t₀| := by
        have hh := mul_le_mul_of_nonneg_left ht10 (by positivity : 0 ≤ 4 / k)
        have heq : 4 / k * (k / 2) = 2 := by field_simp; ring
        rwa [heq] at hh
  have hav : a * (t₁ - t₀) = c := div_mul_cancel₀ _ htne
  have heq : q - (1 / 2 : ℝ) • (q₀ + q₁) - a • (q₁ - q₀) =
      E - (1 / 2 : ℝ) • (e₀ + e₁) - a • (e₁ - e₀) := by
    dsimp [E, e₀, e₁]
    have hc' : c = 2 * t - 1 / 2 - (t₀ + t₁) / 2 := rfl
    match_scalars <;> dsimp [c] at hav <;> nlinarith only [hav]
  refine ⟨a, ha, ?_⟩
  rw [heq]
  calc
    _ ≤ ‖E - (1 / 2 : ℝ) • (e₀ + e₁)‖ + ‖a • (e₁ - e₀)‖ := norm_sub_le _ _
    _ ≤ (‖E‖ + ‖(1 / 2 : ℝ) • (e₀ + e₁)‖) + |a| * ‖e₁ - e₀‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact norm_sub_le _ _
    _ ≤ 3 * ρ + (4 / k) * (2 * ρ) := by
      exact add_le_add (by linarith) (mul_le_mul ha he10.le (norm_nonneg _) (by positivity))
    _ ≤ 11 * ρ / k := by
      apply (le_div_iff₀ hk).mpr
      have hh := mul_le_mul_of_nonneg_left hk1 (by positivity : 0 ≤ 3 * ρ)
      field_simp
      nlinarith

lemma affine_midpoint (f : Space ≃ᴬ[ℝ] Space) (x v : Space) :
    f (x + (1 / 2 : ℝ) • v) = (1 / 2 : ℝ) • (f x + f (x + v)) := by
  have h := f.toAffineEquiv.toAffineMap.apply_lineMap x (x + v) (1 / 2 : ℝ)
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left] at h
  change f ((1 / 2 : ℝ) • v + x) = (1 / 2 : ℝ) • (f (x + v) - f x) + f x at h
  rw [add_comm ((1 / 2 : ℝ) • v) x] at h
  rw [h]
  module

lemma affine_residual (f : Space ≃ᴬ[ℝ] Space) (x v q : Space) (a : ℝ) :
    f (q - a • v) - f (x + (1 / 2 : ℝ) • v) =
      f q - f (x + (1 / 2 : ℝ) • v) - a • (f (x + v) - f x) := by
  have h₁ := f.toAffineEquiv.toAffineMap.linearMap_vsub (q - a • v) q
  have h₂ := f.toAffineEquiv.toAffineMap.linearMap_vsub (x + v) x
  simp only [vsub_eq_sub] at h₁ h₂
  have hvec : q - a • v - q = (-a) • v := by module
  rw [hvec, map_smul] at h₁
  rw [add_sub_cancel_left] at h₂
  rw [h₂] at h₁
  have he : f (q - a • v) = -a • (f (x + v) - f x) + f q := by
    convert (eq_sub_iff_add_eq.mp h₁).symm using 1 <;> rfl
  rw [he]
  module

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
