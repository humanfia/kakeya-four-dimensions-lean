import Submission.Obl.k4_dyadic_crop_affine_laws.CropDensities

/- The selected-law and pullback arguments adapt this LOT tree, o091,
session x0299, commit 918e44e, BaseChange.lean and RawDensity.lean.
The affine equivalences themselves are imported from accepted o090. -/

namespace Submission.Obl.k4_crop_base_finite_tail.BaseTransport

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_affine_laws

noncomputable def stateEquiv (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ) : Inc ≃ᵐ Inc :=
  (Framework.cropTrajectoryEquiv a ha.ne'
    ![a * (q 0 : ℝ), a * (q 1 : ℝ)]
    ![a * (q 2 : ℝ), a * (q 3 : ℝ)]).symm.prodCongr (MeasurableEquiv.refl ℝ)

lemma stateEquiv_apply (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ) (x : Inc) :
    stateEquiv a ha q x = CropInc a q x := by
  change (_, x.2) = (Crop a q x.1, x.2)
  rw [Crop_eq_cropTrajectoryEquiv_symm ha]
  rfl

noncomputable def obsEquiv (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ) : Base ≃ᵐ Base :=
  (Framework.cropBaseEquiv a ha.ne'
    ![a * (q 0 : ℝ), a * (q 1 : ℝ)]
    ![a * (q 2 : ℝ), a * (q 3 : ℝ)]).symm.prodCongr (MeasurableEquiv.refl ℤ)

lemma map_obs_reference (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ) :
    BaseRef.map (obsEquiv a ha q) = ENNReal.ofReal (a^2) • BaseRef := by
  exact Framework.map_prod_count_equiv _ volume volume _
    (Framework.map_cropBaseEquiv_symm a ha _ _)

lemma obs_crop (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ)
    (N : ℕ → ℝ) (k : ℕ) (r : ℝ) (x : Inc) :
    Obs N k r (stateEquiv a ha q x) = obsEquiv a ha q (Obs N k r x) := by
  let c : Fin 2 → ℝ := ![a * (q 0 : ℝ), a * (q 1 : ℝ)]
  let v : Fin 2 → ℝ := ![a * (q 2 : ℝ), a * (q 3 : ℝ)]
  let e := Framework.cropTrajectoryEquiv a ha.ne' c v
  let b := (Framework.cropBaseEquiv a ha.ne' c v).prodCongr (MeasurableEquiv.refl ℤ)
  apply b.injective
  have hf := Framework.crop_pureObservation a ha.ne' c v 1 (Scale N k r)
    (e.symm x.1, x.2)
  have hObs (z : Inc) : Framework.pureObservation 1 (Scale N k r) z = Obs N k r z := by
    simp only [Framework.pureObservation, one_mul]
    rfl
  rw [hObs, hObs] at hf
  change b (Obs N k r (e.symm x.1, x.2)) = b (b.symm (Obs N k r x))
  rw [b.apply_symm_apply]
  simpa only [e, MeasurableEquiv.apply_symm_apply] using hf.symm

lemma selected_transport (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ)
    (ν : Measure Line) [SFinite ν] (E : Set Inc) (c : ENNReal) :
    Selected (c • (ν.restrict (Cell a q)).map (Crop a q))
      (CropInc a q '' (E ∩ (Cell a q ×ˢ univ))) =
      c • ((Selected ν E).restrict (Cell a q ×ˢ univ)).map (stateEquiv a ha q) := by
  unfold Selected
  rw [Measure.prod_smul_left, Measure.restrict_smul]
  congr 1
  have hp : ((ν.restrict (Cell a q)).map (Crop a q)).prod volume =
      ((ν.restrict (Cell a q)).prod volume).map (CropInc a q) := by
    have hfun : Prod.map (Crop a q) (id : ℝ → ℝ) = CropInc a q := by
      funext x
      rfl
    rw [← hfun]
    simpa only [Measure.map_id] using
      Measure.map_prod_map (ν.restrict (Cell a q)) (volume : Measure ℝ)
        (by rw [Crop_eq_cropTrajectoryEquiv_symm ha]; exact MeasurableEquiv.measurable _)
        (measurable_id : Measurable (id : ℝ → ℝ))
  have hT : CropInc a q = stateEquiv a ha q := (funext (stateEquiv_apply a ha q)).symm
  rw [hp, hT, Measure.restrict_prod_eq_prod_univ,
    (stateEquiv a ha q).restrict_map, preimage_image_eq _ (stateEquiv a ha q).injective,
    Measure.restrict_restrict_of_subset inter_subset_right,
    Measure.restrict_restrict ((measurableSet_Cell a q).prod MeasurableSet.univ),
    inter_comm (Cell a q ×ˢ univ) E]

lemma selected_transport_apply (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ)
    (ν : Measure Line) [SFinite ν] (E : Set Inc) {p : ℝ} (hp : 0 < p) (S : Set Inc) :
    ENNReal.ofReal p *
      Selected ((ENNReal.ofReal p)⁻¹ • (ν.restrict (Cell a q)).map (Crop a q))
        (CropInc a q '' (E ∩ (Cell a q ×ˢ univ))) S =
      (Selected ν E).restrict (Cell a q ×ˢ univ) (stateEquiv a ha q ⁻¹' S) := by
  rw [selected_transport a ha q ν E, Measure.smul_apply, smul_eq_mul,
    (stateEquiv a ha q).map_apply, ← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, one_mul]

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
  rw [hraw, Framework.map_withDensity_measurableEquiv
    e.symm σ G hG, map_inverse_reference e ρ σ J hJ hJt hbase,
    withDensity_smul_measure, smul_smul]
  have hm : Measurable (fun x => G (e x)) := hG.comp e.measurable
  simp only [MeasurableEquiv.symm_symm]
  rw [← withDensity_smul _ hm]
  congr 1

lemma raw_density_law (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ)
    (N : ℕ → ℝ) (k : ℕ) (r p : ℝ) (hp : 0 < p)
    (μ : Measure Inc) (G : Base → ENNReal) (hG : Measurable G)
    (hlaw : ((ENNReal.ofReal p)⁻¹ • μ.map (stateEquiv a ha q)).map (Obs N k r) =
      BaseRef.withDensity G) :
    μ.map (Obs N k r) = BaseRef.withDensity
      (fun z => (ENNReal.ofReal p / ENNReal.ofReal (a^2)) * G (obsEquiv a ha q z)) := by
  rw [Measure.map_smul _ (measurable_Obs N k r).aemeasurable,
    Measure.map_map (measurable_Obs N k r) (stateEquiv a ha q).measurable,
    show Obs N k r ∘ stateEquiv a ha q = obsEquiv a ha q ∘ Obs N k r
      from funext (obs_crop a ha q N k r),
    ← Measure.map_map (obsEquiv a ha q).measurable (measurable_Obs N k r)] at hlaw
  exact pullback_density_law _ _ _ _ _
    (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos ha)) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
    (map_obs_reference a ha q) _ G hG hlaw

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

lemma crop_bad_mass_eq (a : ℝ) (ha : 0 < a) (q : Fin 4 → ℤ)
    (N : ℕ → ℝ) (k : ℕ) (r p : ℝ) (hp : 0 < p)
    (ν : Measure Line) [SFinite ν] (E : Set Inc)
    (G : Base → ENNReal) (lo hi δ : ℝ) :
    let raw : Base → ENNReal := fun z =>
      (ENNReal.ofReal p / ENNReal.ofReal (a^2)) * G (obsEquiv a ha q z)
    ENNReal.ofReal p *
      Selected ((ENNReal.ofReal p)⁻¹ • (ν.restrict (Cell a q)).map (Crop a q))
        (CropInc a q '' (E ∩ (Cell a q ×ˢ univ)))
          {x | G (Obs N k r x) < ENNReal.ofReal ((a^2 / p) * δ * lo) ∨
            ENNReal.ofReal ((a^2 / p) * hi / δ) < G (Obs N k r x)} =
      (Selected ν E).restrict (Cell a q ×ˢ univ)
        {x | raw (Obs N k r x) < ENNReal.ofReal (δ * lo) ∨
          ENNReal.ofReal (hi / δ) < raw (Obs N k r x)} := by
  dsimp only
  rw [selected_transport_apply a ha q ν E hp]
  apply congrArg ((Selected ν E).restrict (Cell a q ×ˢ univ))
  ext x
  change (G (Obs N k r (stateEquiv a ha q x)) < _ ∨
    _ < G (Obs N k r (stateEquiv a ha q x))) ↔ _
  rw [obs_crop a ha q N k r]
  exact (raw_density_window_iff ha hp _ lo hi δ).symm

end Submission.Obl.k4_crop_base_finite_tail.BaseTransport
