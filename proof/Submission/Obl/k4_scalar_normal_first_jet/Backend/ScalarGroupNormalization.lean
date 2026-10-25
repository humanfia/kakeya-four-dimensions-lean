/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGroupNormalization.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGroupNormalization.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp

/-! A temporary scalar group is selected and scaled by its prescribed
geometric weight. Original trajectory and incidence masses remain explicit. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

noncomputable def scalarGroupPrior {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (code : Λ → β) (b : β) (c : ℝ) : Measure Λ :=
  ENNReal.ofReal c⁻¹ • ν.restrict (code ⁻¹' {b})

theorem scalarGroupPrior_finite {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (code : Λ → β) (b : β) (c : ℝ) :
    IsFiniteMeasure (scalarGroupPrior ν code b c) :=
  Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem scalarGroupPrior_real {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (code : Λ → β) (b : β) {c : ℝ} (hc : 0 < c)
    {A : Set Λ} (hA : MeasurableSet A) :
    (scalarGroupPrior ν code b c).real A = ν.real (A ∩ code ⁻¹' {b}) / c := by
  simp only [scalarGroupPrior, Measure.real, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_pos.mpr hc).le,
    Measure.restrict_apply hA, div_eq_mul_inv, mul_comm]

theorem original_scalar_group_real {Λ β : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (A : Set Λ) (code : Λ → β) (b : β) {c : ℝ} (hc : 0 < c)
    {T : Set Λ} (hT : MeasurableSet T) (hsub : T ⊆ A ∩ (code ⁻¹' {b})) :
    (scalarGroupPrior (ν.restrict A) code b c).real T = ν.real T / c := by
  rw [scalarGroupPrior_real _ code b hc hT,
    inter_eq_left.mpr (fun l hl => (hsub hl).2)]
  rw [Measure.real, Measure.restrict_apply hT, inter_eq_left.mpr (fun l hl => (hsub hl).1)]
  rfl

theorem original_scalar_group_mass {Θ Λ β : Type*} [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [SFinite μ] (ν : Measure Λ) [SFinite ν] (code : Λ → β) (b : β)
    {c : ℝ} (hc : 0 < c) {E : Set (Θ × Λ)} (hE : MeasurableSet E) :
    (μ.prod (scalarGroupPrior ν code b c)).real E =
      (μ.prod ν).real (E ∩ (univ ×ˢ (code ⁻¹' {b}))) / c := by
  have hprod : μ.prod (ν.restrict (code ⁻¹' {b})) =
      (μ.prod ν).restrict (univ ×ˢ (code ⁻¹' {b})) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := ν) univ (code ⁻¹' {b}))
  simp only [scalarGroupPrior, Measure.prod_smul_right, hprod, Measure.real,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_pos.mpr hc).le, Measure.restrict_apply hE,
    div_eq_mul_inv, mul_comm]

theorem exists_original_normalized_scalar_group {Θ Λ β : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Θ) [IsFiniteMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) (code : Λ → β) (hcode : Measurable code)
    (J : Finset β) {c K δ : ℝ} (hc : 0 < c) (hK : 0 < K) (hδ : 0 < δ)
    (hcover : ∀ p ∈ E, code p.2 ∈ J) (hmass : δ ≤ (μ.prod ν).real E)
    (hcard : (J.card : ℝ) ≤ K / c)
    (hcap : ∀ b ∈ J, ν.real (code ⁻¹' {b}) ≤ K * c) :
    ∃ b ∈ J, (scalarGroupPrior ν code b c).real univ ≤ K ∧
      δ / K ≤ (μ.prod (scalarGroupPrior ν code b c)).real E := by
  obtain ⟨b, hb, hmassb⟩ := exists_heavy_original_cell (μ.prod ν) E (fun p => code p.2) J
    (Filter.Eventually.of_forall hcover) hδ hmass hcard
  refine ⟨b, hb, ?_, ?_⟩
  · rw [scalarGroupPrior_real ν code b hc MeasurableSet.univ, univ_inter]
    exact (div_le_iff₀ hc).mpr (hcap b hb)
  · rw [original_scalar_group_mass μ ν code b hc hE]
    apply (le_div_iff₀ hc).mpr
    have he : E ∩ (fun p : Θ × Λ => code p.2) ⁻¹' {b} = E ∩ (univ ×ˢ (code ⁻¹' {b})) := by
      ext p
      simp
    rw [he] at hmassb
    have hdiv : δ / (K / c) = (δ / K) * c := by field_simp
    simpa only [hdiv] using hmassb

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
