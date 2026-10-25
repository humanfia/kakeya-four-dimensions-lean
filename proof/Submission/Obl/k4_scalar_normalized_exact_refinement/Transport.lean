import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The time coordinate used by a normalized chart. -/
def timeEquiv (t₀ dt : ℝ) (hdt : dt ≠ 0) : ℝ ≃ᵐ ℝ :=
  (MeasurableEquiv.addRight (-t₀)).trans
    (MeasurableEquiv.mulLeft₀ dt⁻¹ (inv_ne_zero hdt))

lemma timeEquiv_apply (t₀ dt : ℝ) (hdt : dt ≠ 0) (t : ℝ) :
    timeEquiv t₀ dt hdt t = (t - t₀) / dt := by
  change dt⁻¹ * (t + -t₀) = _
  ring

lemma map_timeEquiv (t₀ dt : ℝ) (hdt : 0 < dt) :
    (volume : Measure ℝ).map (timeEquiv t₀ dt hdt.ne') =
      ENNReal.ofReal dt • volume := by
  change (volume : Measure ℝ).map
    ((fun t : ℝ => dt⁻¹ * t) ∘ (fun t : ℝ => t + -t₀)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
    Real.map_volume_mul_left (inv_ne_zero hdt.ne')]
  simp [abs_of_pos hdt]

/-- Conditioning on the whole assignment and changing time gives the selected
law with its original prior mass and the exact time Jacobian. -/
theorem normalized_selected_transport {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [SFinite ν] (A : Set X) (C : Set (X × ℝ))
    (hC : MeasurableSet C) (hCA : C ⊆ A ×ˢ univ)
    (e : X ≃ᵐ Y) (t₀ dt : ℝ) (hdt : 0 < dt) :
    ((((ν A)⁻¹ • (ν.restrict A).map e).prod volume).restrict
      ((e.prodCongr (timeEquiv t₀ dt hdt.ne')) '' C)) =
      (ENNReal.ofReal dt * ν A)⁻¹ •
        (((ν.prod volume).restrict C).map (e.prodCongr (timeEquiv t₀ dt hdt.ne'))) := by
  let eT := e.prodCongr (timeEquiv t₀ dt hdt.ne')
  let c := ENNReal.ofReal dt
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdt
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hprod : ((ν.restrict A).prod volume).map eT =
      c • ((ν.restrict A).map e).prod volume := by
    change ((ν.restrict A).prod volume).map (Prod.map e (timeEquiv t₀ dt hdt.ne')) = _
    rw [← Measure.map_prod_map (ν.restrict A) volume e.measurable
      (timeEquiv t₀ dt hdt.ne').measurable, map_timeEquiv t₀ dt hdt, Measure.prod_smul_right]
  have hpr : ((ν.restrict A).prod (volume : Measure ℝ)).restrict C =
      (ν.prod volume).restrict C := by
    have hbase : (ν.restrict A).prod (volume : Measure ℝ) =
        (ν.prod volume).restrict (A ×ˢ univ) := by
      simpa only [Measure.restrict_univ] using
        (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) A univ)
    rw [hbase, Measure.restrict_restrict_of_subset hCA]
  have hmap : ((ν.prod volume).restrict C).map eT =
      c • (((ν.restrict A).map e).prod volume).restrict (eT '' C) := by
    rw [← hpr]
    calc
      _ = (((ν.restrict A).prod volume).map eT).restrict (eT '' C) := by
        rw [Measure.restrict_map eT.measurable (eT.measurableSet_image.mpr hC),
          Set.preimage_image_eq _ eT.injective]
      _ = _ := by rw [hprod, Measure.restrict_smul]
  change (((ν A)⁻¹ • (ν.restrict A).map e).prod volume).restrict (eT '' C) =
    (c * ν A)⁻¹ • (((ν.prod volume).restrict C).map eT)
  rw [Measure.prod_smul_left, Measure.restrict_smul, hmap, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    (ν A)⁻¹ = (ν A)⁻¹ * (c⁻¹ * c) := by rw [ENNReal.inv_mul_cancel hc hct, mul_one]
    _ = c⁻¹ * (ν A)⁻¹ * c := by ac_rfl

theorem normalized_selected_transport_restrict {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [SFinite ν] (E : Set (X × ℝ)) (A : Set X) (C : Set (X × ℝ))
    (hC : MeasurableSet C) (hCA : C ⊆ A ×ˢ univ) (hCE : C ⊆ E)
    (e : X ≃ᵐ Y) (t₀ dt : ℝ) (hdt : 0 < dt) :
    ((((ν A)⁻¹ • (ν.restrict A).map e).prod volume).restrict
      ((e.prodCongr (timeEquiv t₀ dt hdt.ne')) '' C)) =
      (ENNReal.ofReal dt * ν A)⁻¹ •
        ((((ν.prod volume).restrict E).restrict C).map
          (e.prodCongr (timeEquiv t₀ dt hdt.ne'))) := by
  rw [Measure.restrict_restrict_of_subset hCE]
  exact normalized_selected_transport ν A C hC hCA e t₀ dt hdt

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
