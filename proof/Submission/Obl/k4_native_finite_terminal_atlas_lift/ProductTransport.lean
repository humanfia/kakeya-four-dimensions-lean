/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/ProductTransport.lean. Earlier provenance comments are retained. -/
/- The one-dimensional time equivalence and its Haar calculation are adapted
from same-tree o006, x0006, Framework/ChartProductTransport.lean in the
Submission/Obl/k4_core directory (branch x0006, inspected 2026-10-21).
The original proof uses only Mathlib. The coefficient map below is generic. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.Definitions
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.Conditioning

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

open MeasureTheory Set
open scoped ENNReal

noncomputable def timeEquiv (t₀ q : ℝ) (hq : q ≠ 0) : ℝ ≃ᵐ ℝ where
  toFun τ := t₀ + q * τ
  invFun t := (t - t₀) / q
  left_inv τ := by dsimp; field_simp [hq]; ring
  right_inv t := by dsimp; field_simp [hq]; ring
  measurable_toFun := by change Measurable (fun τ : ℝ => t₀ + q * τ); fun_prop
  measurable_invFun := by change Measurable (fun t : ℝ => (t - t₀) / q); fun_prop

theorem map_timeEquiv_symm (t₀ q : ℝ) (hq : 0 < q) :
    (volume : Measure ℝ).map (timeEquiv t₀ q hq.ne').symm =
      ENNReal.ofReal q • volume := by
  have hcomp : (fun t : ℝ => (t - t₀) / q) =
      (fun t => q⁻¹ * t) ∘ (fun t => t - t₀) := by
    funext t
    simp [div_eq_mul_inv, mul_comm]
  have hsub : Measurable (fun t : ℝ => t - t₀) := by fun_prop
  have hmul : Measurable (fun t : ℝ => q⁻¹ * t) := by fun_prop
  change volume.map (fun t : ℝ => (t - t₀) / q) = _
  rw [hcomp, ← Measure.map_map hmul hsub,
    (measurePreserving_sub_right volume t₀).map_eq,
    Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv, abs_of_pos hq]

/-- Physical-to-normalized incidence coordinates for an arbitrary native
coefficient equivalence. -/
noncomputable def normalizedIncidenceEquiv (θ : Trajectory ≃ᵐ Trajectory)
    (t₀ q : ℝ) (hq : q ≠ 0) : Incidence ≃ᵐ Incidence :=
  θ.prodCongr (timeEquiv t₀ q hq).symm

theorem normalizedIncidenceEquiv_apply (θ : Trajectory ≃ᵐ Trajectory)
    (t₀ q : ℝ) (hq : q ≠ 0) (z : Incidence) :
    normalizedIncidenceEquiv θ t₀ q hq z = (θ z.1, (z.2 - t₀) / q) := rfl

theorem normalizedIncidenceEquiv_symm_apply (θ : Trajectory ≃ᵐ Trajectory)
    (t₀ q : ℝ) (hq : q ≠ 0) (z : Incidence) :
    (normalizedIncidenceEquiv θ t₀ q hq).symm z = (θ.symm z.1, t₀ + q * z.2) := rfl

theorem map_assigned_product (ν : Measure Trajectory) [SFinite ν]
    (A : Set Trajectory) (θ : Trajectory ≃ᵐ Trajectory)
    (t₀ q : ℝ) (hq : 0 < q) :
    ((ν.restrict A).prod volume).map (normalizedIncidenceEquiv θ t₀ q hq.ne') =
      ENNReal.ofReal q • ((ν.restrict A).map θ).prod volume := by
  change ((ν.restrict A).prod volume).map (Prod.map θ (timeEquiv t₀ q hq.ne').symm) = _
  rw [← Measure.map_prod_map (ν.restrict A) volume θ.measurable
    (timeEquiv t₀ q hq.ne').symm.measurable, map_timeEquiv_symm t₀ q hq,
    Measure.prod_smul_right]

/-- Recover the original within-world assigned product law. The factor is
block length times the FULL prior assignment mass. -/
theorem map_assigned_product_conditioned (ν : Measure Trajectory) [SFinite ν]
    (A : Set Trajectory) (hA : ν A ≠ 0) (hAfin : ν A ≠ ∞)
    (θ : Trajectory ≃ᵐ Trajectory) (t₀ q : ℝ) (hq : 0 < q) :
    ((ν.restrict A).prod volume).map (normalizedIncidenceEquiv θ t₀ q hq.ne') =
      (ENNReal.ofReal q * ν A) •
        (Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior ν A θ).prod
          volume := by
  rw [map_assigned_product ν A θ t₀ q hq,
    Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior,
    Measure.prod_smul_left, smul_smul]
  rw [mul_assoc, ENNReal.mul_inv_cancel hA hAfin, mul_one]

/-- A measurable child assignment is charged to its exact original prior,
without a selected-incidence renormalization. -/
theorem assigned_product_pullback (ν : Measure Trajectory) [SFinite ν]
    (A : Set Trajectory) (hAmeas : MeasurableSet A) (hA : ν A ≠ 0) (hAfin : ν A ≠ ∞)
    (θ : Trajectory ≃ᵐ Trajectory) (t₀ q : ℝ) (hq : 0 < q)
    (F : Set Incidence) (hF : MeasurableSet F) :
    (ν.prod volume) ((A ×ˢ univ) ∩ normalizedIncidenceEquiv θ t₀ q hq.ne' ⁻¹' F) =
      (ENNReal.ofReal q * ν A) *
        ((Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior ν A θ).prod
          volume) F := by
  have h := congrArg (fun μ : Measure Incidence => μ F)
    (map_assigned_product_conditioned ν A hA hAfin θ t₀ q hq)
  rw [(normalizedIncidenceEquiv θ t₀ q hq.ne').measurableEmbedding.map_apply,
    Measure.smul_apply, smul_eq_mul] at h
  have hprod : (ν.restrict A).prod (volume : Measure ℝ) =
      (ν.prod volume).restrict (A ×ˢ univ) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) A univ)
  rw [hprod, Measure.restrict_apply
    ((normalizedIncidenceEquiv θ t₀ q hq.ne').measurable hF)] at h
  simpa only [inter_comm] using h

end Submission.Obl.k4_native_finite_terminal_atlas_lift
