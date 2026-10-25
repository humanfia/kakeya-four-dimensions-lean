/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/TimeConditioning.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning

/-! The product-prior budget of normalization includes the time-block length. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_dyadic_crop_affine_laws.Framework

noncomputable def timeChartEquiv (t₀ q : ℝ) (hq : q ≠ 0) : ℝ ≃ᵐ ℝ :=
  (MeasurableEquiv.mulLeft₀ q hq).trans (MeasurableEquiv.addRight t₀)

theorem timeChartEquiv_apply (t₀ q : ℝ) (hq : q ≠ 0) (τ : ℝ) :
    timeChartEquiv t₀ q hq τ = q * τ + t₀ := rfl

theorem timeChartEquiv_symm_apply (t₀ q : ℝ) (hq : q ≠ 0) (t : ℝ) :
    (timeChartEquiv t₀ q hq).symm t = q⁻¹ * (t - t₀) := by
  simp [timeChartEquiv, sub_eq_add_neg]

theorem map_timeChartEquiv_symm (t₀ q : ℝ) (hq : 0 < q) :
    (volume : Measure ℝ).map (timeChartEquiv t₀ q hq.ne').symm = ENNReal.ofReal q • volume := by
  have heq : ((timeChartEquiv t₀ q hq.ne').symm : ℝ → ℝ) =
      (fun t : ℝ => q⁻¹ * t) ∘ (fun t : ℝ => t - t₀) := by
    funext t
    exact timeChartEquiv_symm_apply t₀ q hq.ne' t
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), map_sub_right_eq_self,
    Real.map_volume_mul_left (inv_ne_zero hq.ne')]
  simp only [inv_inv, abs_of_pos hq]

/-- Apply the trajectory change and normalize the time interval together. -/
noncomputable def normalizedIncidenceEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (t₀ q : ℝ) (hq : q ≠ 0) : (X × ℝ) ≃ᵐ (Y × ℝ) :=
  e.prodCongr (timeChartEquiv t₀ q hq).symm

/-- The exact original product-prior budget is q times the unchanged assigned prior mass. -/
theorem assigned_product_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [SFinite ν] (A : Set X) (e : X ≃ᵐ Y)
    (t₀ q : ℝ) (hq : 0 < q) (hA0 : ν A ≠ 0) (hAfin : ν A ≠ ∞) :
    ((ν.prod volume).restrict (A ×ˢ (univ : Set ℝ))).map
      (normalizedIncidenceEquiv e t₀ q hq.ne') =
      (ENNReal.ofReal q * ν A) • ((conditionedPrior ν A e).prod volume) := by
  have hpr : (ν.prod (volume : Measure ℝ)).restrict (A ×ˢ univ) =
      (ν.restrict A).prod volume := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) A univ).symm
  rw [hpr]
  change ((ν.restrict A).prod volume).map (Prod.map e (timeChartEquiv t₀ q hq.ne').symm) = _
  rw [← Measure.map_prod_map (ν.restrict A) volume e.measurable
    (timeChartEquiv t₀ q hq.ne').symm.measurable,
    map_timeChartEquiv_symm t₀ q hq, Measure.prod_smul_right,
    conditionedPrior, Measure.prod_smul_left, smul_smul]
  rw [mul_assoc, ENNReal.mul_inv_cancel hA0 hAfin, mul_one]

/-- Selected incidence mass is divided by the full original product-prior budget. -/
theorem selected_product_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [SFinite ν] (A : Set X) (E : Set (X × ℝ))
    (hE : MeasurableSet E) (hEA : E ⊆ A ×ˢ univ) (e : X ≃ᵐ Y)
    (t₀ q : ℝ) (hq : 0 < q) (hA0 : ν A ≠ 0) (hAfin : ν A ≠ ∞) :
    (((conditionedPrior ν A e).prod volume).restrict
      ((normalizedIncidenceEquiv e t₀ q hq.ne') '' E)) =
      (ENNReal.ofReal q * ν A)⁻¹ •
        (((ν.prod volume).restrict E).map (normalizedIncidenceEquiv e t₀ q hq.ne')) := by
  let f := normalizedIncidenceEquiv e t₀ q hq.ne'
  let budget := ENNReal.ofReal q * ν A
  have hbase := assigned_product_transport ν A e t₀ q hq hA0 hAfin
  have hmap : ((ν.prod volume).restrict E).map f =
      budget • (((conditionedPrior ν A e).prod volume).restrict (f '' E)) := by
    calc
      ((ν.prod volume).restrict E).map f =
          (((ν.prod volume).restrict (A ×ˢ univ)).map f).restrict (f '' E) := by
        rw [Measure.restrict_map f.measurable (f.measurableSet_image.mpr hE),
          preimage_image_eq _ f.injective, Measure.restrict_restrict hE,
          inter_eq_left.mpr hEA]
      _ = _ := by rw [hbase, Measure.restrict_smul]
  have hb0 : budget ≠ 0 := mul_ne_zero (by positivity) hA0
  have hbfin : budget ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
  change _ = budget⁻¹ • _
  rw [hmap, smul_smul, ENNReal.inv_mul_cancel hb0 hbfin, one_smul]

/-- A selected event in the old chart block lies in the new unit time interval. -/
theorem normalized_event_unit_time {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (t₀ q : ℝ) (hq : 0 < q) (E : Set (X × ℝ))
    (hE : E ⊆ univ ×ˢ Icc t₀ (t₀ + q)) :
    (normalizedIncidenceEquiv e t₀ q hq.ne') '' E ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨mem_univ _, ?_⟩
  have ht := (hE hp).2
  change (timeChartEquiv t₀ q hq.ne').symm p.2 ∈ Icc (0 : ℝ) 1
  rw [timeChartEquiv_symm_apply, mul_comm, ← div_eq_mul_inv]
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hq.le, (div_le_one hq).mpr (by linarith [ht.2])⟩

end Submission.Obl.k4_balanced_native_packet_transport.CPF
