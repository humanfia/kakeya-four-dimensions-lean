/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGroupLeftMass.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGroupLeftMass.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGroupNormalization

/-! Read an original anchor-group law with the trajectory coordinate first. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_scalar_group_left_mass {Θ Λ β : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [SFinite μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    (A : Set Λ) (code : Λ → β) (bin : β) {c : ℝ} (hc : 0 < c)
    {E : Set (Λ × Θ)} (hE : MeasurableSet E)
    (hsub : E ⊆ (A ∩ code ⁻¹' {bin}) ×ˢ univ) :
    ((scalarGroupPrior (ν.restrict A) code bin c).prod μ).real E =
      (ν.prod μ).real E / c := by
  let νb := scalarGroupPrior (ν.restrict A) code bin c
  letI : IsFiniteMeasure νb := scalarGroupPrior_finite _ _ _ _
  let P := Prod.swap ⁻¹' E
  have hPm : MeasurableSet P := hE.preimage measurable_swap
  have hswap : (μ.prod νb).real P = (νb.prod μ).real E := by
    have hh := congrArg (fun m : Measure (Λ × Θ) => m E) (Measure.prod_swap (μ := μ) (ν := νb))
    rw [Measure.map_apply measurable_swap hE] at hh
    exact congrArg ENNReal.toReal hh
  have hprod : μ.prod (ν.restrict A) = (μ.prod ν).restrict (univ ×ˢ A) := by
    simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ := μ) (ν := ν) univ A)
  have hPc : P ⊆ univ ×ˢ (code ⁻¹' {bin}) :=
    fun q hq => ⟨mem_univ _, (hsub hq).1.2⟩
  have hPA : P ⊆ univ ×ˢ A := fun q hq => ⟨mem_univ _, (hsub hq).1.1⟩
  have hmass := original_scalar_group_mass μ (ν.restrict A) code bin hc hPm
  rw [inter_eq_left.mpr hPc, hprod] at hmass
  simp only [Measure.real, Measure.restrict_apply hPm, inter_eq_left.mpr hPA] at hmass
  have hh := congrArg (fun m : Measure (Λ × Θ) => m E) (Measure.prod_swap (μ := μ) (ν := ν))
  rw [Measure.map_apply measurable_swap hE] at hh
  calc
    _ = (μ.prod νb).real P := hswap.symm
    _ = (μ.prod ν).real P / c := hmass
    _ = _ := congrArg (fun x : ENNReal => x.toReal / c) hh

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
