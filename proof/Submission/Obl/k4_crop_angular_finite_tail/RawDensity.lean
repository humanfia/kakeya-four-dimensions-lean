/- Adapted from this LOT tree, obligation o091, session x0299, commit 918e44ebabf26b3b2fd56f3cccbf12b4ac1bac6e,
Submission/Obl/k4_dyadic_crop_typicality/RawDensity.lean. Transfer.lean in that branch was written by session x0302 (9db252b). -/

import Submission.Obl.k4_crop_angular_finite_tail.BaseChange
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace Submission.Obl.k4_crop_angular_finite_tail

open Submission.Obl.k4_profile_density_bounds (width observe selected reference)

lemma map_inverse_reference {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (ρ : Measure X) (σ : Measure Y) (J : ENNReal)
    (hJ : J ≠ 0) (hJt : J ≠ ∞) (hmap : ρ.map e = J • σ) :
    σ.map e.symm = J⁻¹ • ρ := by
  have hinv : ρ = J • σ.map e.symm := by
    calc
      ρ = (ρ.map e).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable,
          e.symm_comp_self, Measure.map_id]
      _ = J • σ.map e.symm := by rw [hmap, Measure.map_smul _ e.symm.measurable.aemeasurable]
  rw [hinv, smul_smul, ENNReal.inv_mul_cancel hJ hJt, one_smul]

lemma pullback_density_law {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (ρ : Measure X) (σ : Measure Y) (J p : ENNReal)
    (hJ : J ≠ 0) (hJt : J ≠ ∞) (hp : p ≠ 0) (hpt : p ≠ ∞)
    (hbase : ρ.map e = J • σ)
    (μ : Measure X) (G : Y → ENNReal) (hG : Measurable G)
    (hlaw : p⁻¹ • μ.map e = σ.withDensity G) :
    μ = ρ.withDensity (fun x => (p / J) * G (e x)) := by
  have hraw : μ = p • (σ.withDensity G).map e.symm := by
    rw [← hlaw, Measure.map_smul _ e.symm.measurable.aemeasurable,
      Measure.map_map e.symm.measurable e.measurable,
      e.symm_comp_self, Measure.map_id, smul_smul,
      ENNReal.mul_inv_cancel hp hpt, one_smul]
  rw [hraw, Submission.Obl.k4_dyadic_crop_affine_laws.Framework.map_withDensity_measurableEquiv
    e.symm σ G hG, map_inverse_reference e ρ σ J hJ hJt hbase,
    withDensity_smul_measure, smul_smul]
  have hm : Measurable (fun x => G (e x)) := hG.comp e.measurable
  simp only [MeasurableEquiv.symm_symm]
  rw [← withDensity_smul _ hm]
  congr 1

/-- Pull an arbitrary cropped angular density back to the effective original
angular grid. This gives the unnormalized density of the restricted source law. -/
lemma raw_angular_density_law {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {d : ℕ} (hd : height N (u + v) = height N u + height N v + d)
    (q : Fin 4 → ℤ) (r p : ℝ) (hp : 0 < p)
    (μ : Measure State) (G : Observation → ENNReal) (hG : Measurable G)
    (hlaw : ((ENNReal.ofReal p)⁻¹ • μ.map (cropState (width N u) q)).map (observe N r v) =
      reference.withDensity G) :
    μ.map (observeWidth N r (width N u * width N v)) = reference.withDensity
      (fun z => (ENNReal.ofReal p / ENNReal.ofReal (width N u ^ 2)) *
        G (observationCropEquiv (ne_of_gt (Submission.Obl.k4_profile_density_bounds.width_pos N u))
          q (height N v) z)) := by
  have ha : 0 < width N u := Submission.Obl.k4_profile_density_bounds.width_pos N u
  let e := observationCropEquiv ha.ne' q (height N v)
  have hobs : observe N r v ∘ cropState (width N u) q =
      e ∘ observeWidth N r (width N u * width N v) := by
    funext z
    simp only [Function.comp_apply, observeWidth_product hN hu hv hd]
    exact observe_crop hN hu hv hd q r z
  rw [Measure.map_smul _ (Submission.Obl.k4_profile_density_bounds.measurable_observe N r v).aemeasurable,
    Measure.map_map (Submission.Obl.k4_profile_density_bounds.measurable_observe N r v)
      (measurable_cropState _ _), hobs,
    ← Measure.map_map e.measurable (measurable_observeWidth _ _ _)] at hlaw
  exact pullback_density_law e reference reference _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos ha)) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    (map_observationCrop_reference ha q (height N v)) _ G hG hlaw

lemma density_scale_window_iff {c : ENNReal} (hc : c ≠ 0) (hct : c ≠ ∞)
    (x lo hi : ENNReal) :
    (c⁻¹ * x < lo ∨ hi < c⁻¹ * x) ↔ (x < c * lo ∨ c * hi < x) := by
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl hc) (Or.inl hct),
    ENNReal.lt_div_iff_mul_lt (Or.inl hc) (Or.inl hct)]
  simp only [mul_comm]

lemma raw_density_window_iff {a p : ℝ} (ha : 0 < a) (hp : 0 < p)
    (x : ENNReal) (lo hi δ : ℝ) :
    ((ENNReal.ofReal p / ENNReal.ofReal (a^2)) * x < ENNReal.ofReal (δ * lo) ∨
      ENNReal.ofReal (hi / δ) < (ENNReal.ofReal p / ENNReal.ofReal (a^2)) * x) ↔
    (x < ENNReal.ofReal ((a^2 / p) * δ * lo) ∨
      ENNReal.ofReal ((a^2 / p) * hi / δ) < x) := by
  have hc : 0 < a^2 / p := div_pos (sq_pos_of_pos ha) hp
  have hraw : (ENNReal.ofReal (a^2 / p))⁻¹ = ENNReal.ofReal p / ENNReal.ofReal (a^2) := by
    rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos ha), ← ENNReal.ofReal_inv_of_pos hc]
    congr 1
    field_simp
  have hlo : ENNReal.ofReal (a^2 / p) * ENNReal.ofReal (δ * lo) =
      ENNReal.ofReal ((a^2 / p) * δ * lo) := by
    rw [← ENNReal.ofReal_mul hc.le, mul_assoc]
  have hhi : ENNReal.ofReal (a^2 / p) * ENNReal.ofReal (hi / δ) =
      ENNReal.ofReal ((a^2 / p) * hi / δ) := by
    rw [← ENNReal.ofReal_mul hc.le]
    congr 1
    ring
  simpa only [hraw, hlo, hhi] using density_scale_window_iff
    (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top x
      (ENNReal.ofReal (δ * lo)) (ENNReal.ofReal (hi / δ))

lemma crop_angular_bad_mass_eq {N u v : ℝ} (hN : 1 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    {d : ℕ} (hd : height N (u + v) = height N u + height N v + d)
    (q : Fin 4 → ℤ) (r p : ℝ) (hp : 0 < p)
    (ν : Measure Line) [SFinite ν] (E : Set State)
    (G : Observation → ENNReal) (lo hi δ : ℝ) :
    let a := width N u
    let e := observationCropEquiv (ne_of_gt (Submission.Obl.k4_profile_density_bounds.width_pos N u))
      q (height N v)
    let raw : Observation → ENNReal := fun z =>
      (ENNReal.ofReal p / ENNReal.ofReal (a^2)) * G (e z)
    ENNReal.ofReal p *
      selected ((ENNReal.ofReal p)⁻¹ • (ν.restrict (cropBox a q)).map (cropLine a q))
        (cropState a q '' (E ∩ (cropBox a q ×ˢ univ)))
          {x | G (observe N r v x) < ENNReal.ofReal ((a^2 / p) * δ * lo) ∨
            ENNReal.ofReal ((a^2 / p) * hi / δ) < G (observe N r v x)} =
      (selected ν E).restrict (cropBox a q ×ˢ univ)
        {x | raw (observeWidth N r (a * width N v) x) < ENNReal.ofReal (δ * lo) ∨
          ENNReal.ofReal (hi / δ) < raw (observeWidth N r (a * width N v) x)} := by
  dsimp only
  have ha := Submission.Obl.k4_profile_density_bounds.width_pos N u
  rw [selected_crop_apply ha.ne' q ν E hp]
  apply congrArg ((selected ν E).restrict (cropBox (width N u) q ×ˢ univ))
  ext x
  change (G (observe N r v (cropState (width N u) q x)) < _ ∨
    _ < G (observe N r v (cropState (width N u) q x))) ↔ _
  simp only [mem_ofPred_eq]
  rw [observe_crop hN hu hv hd q r x, observeWidth_product hN hu hv hd r x]
  exact (raw_density_window_iff ha hp _ lo hi δ).symm

end Submission.Obl.k4_crop_angular_finite_tail
