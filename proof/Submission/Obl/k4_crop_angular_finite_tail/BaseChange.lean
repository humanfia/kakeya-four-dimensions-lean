/- Adapted from this LOT tree, obligation o091, session x0299, commit 918e44ebabf26b3b2fd56f3cccbf12b4ac1bac6e,
Submission/Obl/k4_dyadic_crop_typicality/BaseChange.lean. Transfer.lean in that branch was written by session x0302 (9db252b). -/

import Submission.Obl.k4_crop_angular_finite_tail.Observations
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.AffineCrop

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace Submission.Obl.k4_crop_angular_finite_tail

open Submission.Obl.k4_profile_density_bounds (width base velocity hidden observe selected reference)

/-- The affine crop of the continuous base has Jacobian `a⁻²`, so its
pushforward of Lebesgue measure has density `a²`. -/
lemma map_cropBase_volume {a : ℝ} (ha : 0 < a) (q : Fin 4 → ℤ) :
    (volume : Measure Base).map (cropBase a q) = ENNReal.ofReal (a ^ 2) • volume := by
  let c : Fin 2 → ℝ := ![a * (q 0 : ℝ), a * (q 1 : ℝ)]
  let v : Fin 2 → ℝ := ![a * (q 2 : ℝ), a * (q 3 : ℝ)]
  have he : cropBase a q =
      (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.cropBaseEquiv a ha.ne' c v).symm := by
    funext z
    apply (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.cropBaseEquiv a ha.ne' c v).injective
    rw [MeasurableEquiv.apply_symm_apply,
      Submission.Obl.k4_dyadic_crop_affine_laws.Framework.cropBaseEquiv_apply]
    ext j
    fin_cases j <;> simp [c, v, cropBase] <;> field_simp <;> ring
  rw [he]
  exact Submission.Obl.k4_dyadic_crop_affine_laws.Framework.map_cropBaseEquiv_symm a ha c v

lemma selected_crop {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ)
    (ν : Measure Line) [SFinite ν] (E : Set State) (c : ENNReal) :
    selected (c • (ν.restrict (cropBox a q)).map (cropLine a q))
        (cropState a q '' (E ∩ (cropBox a q ×ˢ univ))) =
      c • ((selected ν E).restrict (cropBox a q ×ˢ univ)).map (cropState a q) := by
  unfold selected
  rw [Measure.prod_smul_left, Measure.restrict_smul]
  congr 1
  have hp : ((ν.restrict (cropBox a q)).map (cropLine a q)).prod volume =
      ((ν.restrict (cropBox a q)).prod volume).map (cropState a q) := by
    have hfun : Prod.map (cropLine a q) (id : ℝ → ℝ) = cropState a q := by
      funext p
      rfl
    simpa only [Measure.map_id, hfun] using
      Measure.map_prod_map (ν.restrict (cropBox a q)) (volume : Measure ℝ)
        (measurable_cropLine a q) measurable_id
  rw [hp, Measure.restrict_prod_eq_prod_univ]
  change (((ν.prod volume).restrict (cropBox a q ×ˢ univ)).map (cropStateEquiv ha q)).restrict
      (cropStateEquiv ha q '' (E ∩ (cropBox a q ×ˢ univ))) = _
  rw [(cropStateEquiv ha q).restrict_map, preimage_image_eq _ (cropStateEquiv ha q).injective,
    Measure.restrict_restrict_of_subset inter_subset_right,
    Measure.restrict_restrict ((measurableSet_cropBox a q).prod MeasurableSet.univ),
    inter_comm (cropBox a q ×ˢ univ) E]
  rfl

lemma map_baseObservationCrop_reference {a : ℝ} (ha : 0 < a) (q : Fin 4 → ℤ) :
    baseReference.map (baseObservationCropEquiv ha.ne' q) =
      ENNReal.ofReal (a ^ 2) • baseReference := by
  exact Submission.Obl.k4_dyadic_crop_affine_laws.Framework.map_prod_count_equiv
    (cropBaseEquiv ha.ne' q) volume volume _ (map_cropBase_volume ha q)

lemma map_shiftBins_count (h : ℕ) (q : Fin 4 → ℤ) :
    (Measure.count : Measure VelocityBin).map (shiftBinsEquiv h q) = Measure.count := by
  change (Measure.count : Measure VelocityBin).map
    (fun v => v - (fun j => q (j.natAdd 2) * (2 : ℤ)^h)) = Measure.count
  exact (measurePreserving_sub_right Measure.count _).map_eq

lemma map_observationCrop_reference {a : ℝ} (ha : 0 < a) (q : Fin 4 → ℤ) (h : ℕ) :
    reference.map (observationCropEquiv ha.ne' q h) = ENNReal.ofReal (a ^ 2) • reference := by
  change (baseReference.prod Measure.count).map
    (Prod.map (baseObservationCropEquiv ha.ne' q) (shiftBinsEquiv h q)) = _
  rw [← Measure.map_prod_map baseReference Measure.count
    (baseObservationCropEquiv ha.ne' q).measurable (shiftBinsEquiv h q).measurable,
    map_shiftBins_count, map_baseObservationCrop_reference ha q, Measure.prod_smul_left]
  rfl

lemma selected_crop_apply {a : ℝ} (ha : a ≠ 0) (q : Fin 4 → ℤ)
    (ν : Measure Line) [SFinite ν] (E : Set State) {p : ℝ} (hp : 0 < p) (S : Set State) :
    ENNReal.ofReal p *
      selected ((ENNReal.ofReal p)⁻¹ • (ν.restrict (cropBox a q)).map (cropLine a q))
        (cropState a q '' (E ∩ (cropBox a q ×ˢ univ))) S =
      (selected ν E).restrict (cropBox a q ×ˢ univ) (cropState a q ⁻¹' S) := by
  rw [selected_crop ha q ν E, Measure.smul_apply, smul_eq_mul]
  change ENNReal.ofReal p * ((ENNReal.ofReal p)⁻¹ *
    (((selected ν E).restrict (cropBox a q ×ˢ univ)).map (cropStateEquiv ha q)) S) = _
  rw [(cropStateEquiv ha q).map_apply, ← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, one_mul]
  rfl

end Submission.Obl.k4_crop_angular_finite_tail
