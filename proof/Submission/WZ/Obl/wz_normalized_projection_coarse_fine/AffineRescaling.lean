-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.AffineRescaling.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Shear

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Dilation in the first coordinate of the projection plane. -/
def horizontalScale (ρ : ℝ) (hρ : ρ ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (ρ * p.1, p.2)
  invFun p := (ρ⁻¹ * p.1, p.2)
  left_inv p := by simp [hρ]
  right_inv p := by simp [hρ]
  measurable_toFun := (measurable_const.mul measurable_fst).prodMk measurable_snd
  measurable_invFun := (measurable_const.mul measurable_fst).prodMk measurable_snd

lemma map_horizontalScale (ρ : ℝ) (hρ : ρ ≠ 0) :
    MeasurePreserving (horizontalScale ρ hρ) volume (ENNReal.ofReal |ρ⁻¹| • volume) := by
  have hleft : MeasurePreserving (fun x : ℝ => ρ * x) volume
      (ENNReal.ofReal |ρ⁻¹| • volume) := ⟨by fun_prop, Real.map_volume_mul_left hρ⟩
  have hh := hleft.prod (MeasurePreserving.id (volume : Measure ℝ))
  rw [Measure.prod_smul_left] at hh
  exact hh

/-- Normalize a parameter ball by subtracting its common graph and rescaling horizontally. -/
def normalizeProjection {f : ℝ → ℝ} (hf : Measurable f) (c : ℝ) (q₀ : Space)
    (ρ : ℝ) (hρ : ρ ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (horizontalShear (h := fun z => -(q₀ 0 + c * z + q₀ 1 * f z + q₀ 2 * z * f z))
    (by fun_prop)).trans (horizontalScale ρ⁻¹ (inv_ne_zero hρ))

lemma map_normalizeProjection {f : ℝ → ℝ} (hf : Measurable f) (c : ℝ) (q₀ : Space)
    {ρ : ℝ} (hρ : 0 < ρ) :
    MeasurePreserving (normalizeProjection hf c q₀ ρ hρ.ne') volume
      (ENNReal.ofReal ρ • volume) := by
  have hh := (map_horizontalScale ρ⁻¹ (inv_ne_zero hρ.ne')).comp
    (measurePreserving_horizontalShear (h := fun z =>
      -(q₀ 0 + c * z + q₀ 1 * f z + q₀ 2 * z * f z)) (by fun_prop))
  simpa only [normalizeProjection, MeasurableEquiv.coe_trans, inv_inv, abs_of_pos hρ] using hh

/-- Normalization multiplies outer area by `rho^-1`, even for a nonmeasurable set. -/
lemma volume_normalizeProjection {f : ℝ → ℝ} (hf : Measurable f) (c : ℝ) (q₀ : Space)
    {ρ : ℝ} (hρ : 0 < ρ) (E : Set (ℝ × ℝ)) :
    volume E = ENNReal.ofReal ρ *
      volume (normalizeProjection hf c q₀ ρ hρ.ne' '' E) := by
  have hh := (map_normalizeProjection hf c q₀ hρ).measure_preimage_equiv
    (normalizeProjection hf c q₀ ρ hρ.ne' '' E)
  rw [preimage_image_eq _ (normalizeProjection hf c q₀ ρ hρ.ne').injective] at hh
  exact hh

lemma normalizeProjection_graphStrip {f : ℝ → ℝ} (hf : Measurable f)
    (r c : ℝ) (q₀ q : Space) {ρ : ℝ} (hρ : 0 < ρ) :
    normalizeProjection hf c q₀ ρ hρ.ne' '' graphStrip r f c (q₀ + ρ • q) ⊆
      graphStrip (r / ρ) f 0 q := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨hp.1, ?_⟩
  change |ρ⁻¹ * (p.1 + -(q₀ 0 + c * p.2 + q₀ 1 * f p.2 + q₀ 2 * p.2 * f p.2)) -
    (q 0 + 0 * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2)| ≤ r / ρ
  have he : ρ⁻¹ * (p.1 + -(q₀ 0 + c * p.2 + q₀ 1 * f p.2 + q₀ 2 * p.2 * f p.2)) -
      (q 0 + 0 * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2) =
      (p.1 - ((q₀ + ρ • q) 0 + c * p.2 + (q₀ + ρ • q) 1 * f p.2 +
        (q₀ + ρ • q) 2 * p.2 * f p.2)) / ρ := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hρ]
  exact div_le_div_of_nonneg_right hp.2 hρ.le

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
