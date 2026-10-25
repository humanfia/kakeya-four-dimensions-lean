import Submission.Obl.k4_balanced_native_packet_transport.Definitions
import Submission.Obl.k4_balanced_native_packet_transport.BlockLaws

namespace Submission.Obl.k4_balanced_native_packet_transport

open MeasureTheory Set
open Submission.Obl.k4_native_finite_terminal_atlas_lift
noncomputable section

/-- Restrict the source conditional law, restore its full prior mass, and
change only time. The denominator is the new full prior times block length. -/
def selectedBlockLaw (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc) : Measure Inc :=
  unitBlockLaw ν A t₀ q hq (s • μ.restrict H)

theorem selectedBlockLaw_restore
    (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤) :
    (ENNReal.ofReal q * ν A) •
      Measure.map (fun p : Inc => (p.1, t₀ + q * p.2))
        (selectedBlockLaw ν A t₀ q hq s μ H) = s • μ.restrict H :=
  unitBlockLaw_restore ν A t₀ q hq _ hA hAfin

theorem selectedBlockLaw_budget_mass
    (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤) :
    (ENNReal.ofReal q * ν A) * (selectedBlockLaw ν A t₀ q hq s μ H) univ = s * μ H := by
  rw [selectedBlockLaw, unitBlockLaw_mass, Measure.smul_apply,
    Measure.restrict_apply_univ, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (mul_ne_zero (ENNReal.ofReal_pos.mpr hq).ne' hA)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin), one_mul]

/-- The analytical selection is bounded by the unchanged assigned product. -/
theorem selected_original_law_le_assigned
    (ν : Measure Traj) [SFinite ν] (A : Set Traj)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hsource : s • μ ≤ ν.prod volume) (hsub : H ⊆ A ×ˢ univ) :
    s • μ.restrict H ≤ (ν.restrict A).prod volume := by
  rw [← Measure.restrict_smul]
  have h := Measure.restrict_mono hsub hsource
  simpa only [Measure.restrict_prod_eq_prod_univ] using h

theorem selectedBlockLaw_le_conditional
    (ν : Measure Traj) [SFinite ν] (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hsource : s • μ ≤ ν.prod volume) (hsub : H ⊆ A ×ˢ univ) :
    selectedBlockLaw ν A t₀ q hq s μ H ≤ ((ν A)⁻¹ • ν.restrict A).prod volume :=
  unitBlockLaw_le_conditional ν A t₀ q hq _ hA hAfin
    (selected_original_law_le_assigned ν A s μ H hsource hsub)

theorem selectedBlockLaw_unit_time
    (ν : Measure Traj) (A : Set Traj) (t₀ q : ℝ) (hq : 0 < q)
    (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hsub : H ⊆ univ ×ˢ Icc t₀ (t₀ + q)) :
    selectedBlockLaw ν A t₀ q hq s μ H (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  apply unitBlockLaw_unit_time
  rw [Measure.smul_apply, Measure.restrict_apply
    (MeasurableSet.univ.prod measurableSet_Icc).compl]
  have he : (univ ×ˢ Icc t₀ (t₀ + q))ᶜ ∩ H = ∅ :=
    eq_empty_iff_forall_notMem.mpr (fun p hp => hp.1 (hsub hp.2))
  rw [he, measure_empty, smul_zero]

theorem selectedBlockLaw_ae_assignment
    (ν : Measure Traj) (A : Set Traj) (hA : MeasurableSet A)
    (t₀ q : ℝ) (hq : 0 < q) (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hH : MeasurableSet H) (hsub : H ⊆ A ×ˢ univ) :
    ∀ᵐ p ∂selectedBlockLaw ν A t₀ q hq s μ H, p.1 ∈ A := by
  have hp : ∀ᵐ p ∂s • μ.restrict H, p.1 ∈ A :=
    Measure.ae_smul_measure ((ae_restrict_mem hH).mono (fun p hp => (hsub hp).1)) s
  let e := normalizedIncidenceEquiv (MeasurableEquiv.refl Traj) t₀ q hq.ne'
  have hmap : ∀ᵐ p ∂Measure.map e (s • μ.restrict H), p.1 ∈ A := by
    apply (ae_map_iff e.measurable.aemeasurable (hA.preimage measurable_fst)).mpr
    exact hp
  exact Measure.ae_smul_measure hmap _

/-- All regular scalar-law properties except a mass floor follow directly
from original-law domination and the uniform coefficient bound. -/
theorem selectedBlockLaw_regular
    {N χ d r m S U : ℝ} (hNχ : 1 ≤ N ^ χ)
    (ν : Measure Traj) [SFinite ν] (A : Set Traj)
    (t₀ q : ℝ) (hq : 0 < q) (s : ENNReal) (μ : Measure Inc) (H : Set Inc)
    (hA : ν A ≠ 0) (hAfin : ν A ≠ ⊤)
    (hsource : s • μ ≤ ν.prod volume)
    (hsub : H ⊆ A ×ˢ Icc t₀ (t₀ + q))
    (b : Traj → Fin 5 → ℝ) (hb : Measurable b) (hcoeff : ∀ l i, |b l i| ≤ N ^ χ) :
    RegularScalarLaw N χ d r m S U ((ν A)⁻¹ • ν.restrict A)
      (selectedBlockLaw ν A t₀ q hq s μ H) b := by
  have hprob := Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior_probability
    ν A (MeasurableEquiv.refl Traj) hA hAfin
  have hprob' : IsProbabilityMeasure ((ν A)⁻¹ • ν.restrict A) := by
    unfold Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior at hprob
    change IsProbabilityMeasure ((ν A)⁻¹ • Measure.map id (ν.restrict A)) at hprob
    simpa only [Measure.map_id] using hprob
  refine ⟨hb, hprob', ?_, ?_, hcoeff⟩
  · apply (selectedBlockLaw_le_conditional ν A t₀ q hq s μ H hA hAfin hsource
      (fun p hp => ⟨(hsub hp).1, mem_univ _⟩)).trans
    intro E
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hNχ)
  · exact selectedBlockLaw_unit_time ν A t₀ q hq s μ H
      (fun p hp => ⟨mem_univ _, (hsub hp).2⟩)

end
end Submission.Obl.k4_balanced_native_packet_transport
