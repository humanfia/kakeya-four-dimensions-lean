-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Gain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Gain.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory

lemma aspect_ratio_pos {δ a b z : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hab : a ≤ δ ^ z * b) : 0 < b := by
  have hp : 0 < δ ^ z := Real.rpow_pos_of_pos hδ z
  exact (mul_pos_iff_of_pos_left hp).mp ((hδ.trans_le hδa).trans_le hab)

lemma aspect_ratio_gain {δ a b z ω : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hab : a ≤ δ ^ z * b) (hω : 0 ≤ ω) :
    δ ^ (-(z * ω)) ≤ (b / a) ^ ω := by
  have hp : 0 < δ ^ z := Real.rpow_pos_of_pos hδ z
  have hr : (δ ^ z)⁻¹ ≤ b / a := by
    apply (le_div_iff₀ ha).mpr
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hab)
  have h := Real.rpow_le_rpow (inv_nonneg.mpr hp.le) hr hω
  rwa [← Real.rpow_neg hδ.le, ← Real.rpow_mul hδ.le, neg_mul] at h

/-- The aspect ratio supplies the exponent improvement in Lemma 6.4, Step 3. -/
theorem gain_of_aspectRatio {σ ω ζ₂ : ℝ} (hω : 0 < ω) (hζ₂ : 0 < ζ₂)
    (hestimate : AspectRatioEstimate σ ω) : Gain σ ω ζ₂ := by
  let α : ℝ := ζ₂ * ω / 400
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨ζ₀, hζ₀, H⟩ := hestimate α hα
  refine ⟨α, hα, ζ₀, hζ₀, ?_⟩
  intro ζ₃ hζ₃ hζ₃₀ ε hε
  obtain ⟨A, hA, η, hη, d, hd, H⟩ := H ζ₃ hζ₃ hζ₃₀
  refine ⟨A, hA, η, hη, min d 1, lt_min hd zero_lt_one, ?_⟩
  intro δ hδ hδd n x v Y hn hv hB hover hYm hYT hden hind hstructure
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_right _ _)
  obtain ⟨a, b, hδa, hflat, hb1, p, c, e₁, e₂, e₃, he, hfact⟩ := hstructure
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := aspect_ratio_pos hδ hδa hflat
  have hab : a ≤ b := hflat.trans (by
    simpa using mul_le_mul_of_nonneg_right
      (Real.rpow_le_one hδ.le hδ1 (by positivity : 0 ≤ ζ₂ / 200)) hb.le)
  have hbound := H δ hδ (hδd.trans (min_le_left _ _)) n x v Y
    hn hv hB hover hYm hYT hden hind a b hδa hab hb1 p c e₁ e₂ e₃ he hfact
  apply (ENNReal.ofReal_le_ofReal ?_).trans hbound
  have hgain := aspect_ratio_gain hδ ha hflat hω.le
  have hpow : δ ^ (ω - α + ε) ≤ δ ^ (ω + α) * (b / a) ^ ω := by
    calc
      _ ≤ δ ^ (ω - α) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = δ ^ (ω + α) * δ ^ (-(ζ₂ / 200 * ω)) := by
        rw [← Real.rpow_add hδ]
        congr 1
        dsimp [α]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgain (Real.rpow_nonneg hδ.le _)
  calc
    _ ≤ A * (δ ^ (ω + α) * (b / a) ^ ω) * (n * δ ^ 4) ^ (σ / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left hpow hA.le
    _ = _ := by ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
