/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 2e65ac82f715df53d854782d6e862452630b9dde,
Submission/Obl/k4_scalar_mesh_projection/StarSupport.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.StarSelection

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem measurable_starSample {Ω : Type*} [MeasurableSpace Ω] (i : Fin 4) :
    Measurable (fun z : (Ω × Ω) × (Ω × Ω) => starSample z i) := by
  fin_cases i
  · exact measurable_fst.comp measurable_fst
  · exact measurable_snd.comp measurable_fst
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

theorem measurePreserving_starSample {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (i : Fin 4) :
    MeasurePreserving (fun z : (Ω × Ω) × (Ω × Ω) => starSample z i)
      ((ν.prod ν).prod (ν.prod ν)) ν := by
  fin_cases i
  · exact (measurePreserving_fst (μ := ν) (ν := ν)).comp (measurePreserving_starPair ν 0)
  · exact (measurePreserving_snd (μ := ν) (ν := ν)).comp (measurePreserving_starPair ν 0)
  · exact (measurePreserving_fst (μ := ν) (ν := ν)).comp (measurePreserving_starPair ν 5)
  · exact (measurePreserving_snd (μ := ν) (ν := ν)).comp (measurePreserving_starPair ν 5)

theorem ae_star_all {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (P : Ω → Prop) (hP : ∀ᵐ ω ∂ν, P ω) :
    ∀ᵐ z ∂((ν.prod ν).prod (ν.prod ν)), ∀ i : Fin 4, P (starSample z i) := by
  apply ae_all_iff.mpr
  intro i
  have hmp := measurePreserving_starSample ν i
  apply ae_of_ae_map hmp.measurable.aemeasurable
  rw [hmp.map_eq]
  exact hP

/-- The four samples are drawn at the same original conditioning state.
Every original line property and every shared-state relation survives
the separated-star restriction, with no choice of witnesses. -/
theorem conditional_star_ae_support {Ω Q : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Q] [StandardBorelSpace Q]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → ℝ) (r : ℝ)
    (P : Ω → Prop) (hPm : MeasurableSet {ω | P ω}) (hP : ∀ᵐ ω ∂μ, P ω)
    (R : Ω → Ω → Prop) (hR : MeasurableSet {z : Ω × Ω | R z.1 z.2})
    (hcert : ∀ ω z, state z = state ω → R ω z) :
    let S := conditionalResampling μ state hstate
    let θ := μ ⊗ₘ starKernel S
    let ρ := θ.restrict (Prod.snd ⁻¹' (starBad control r)ᶜ)
    ∀ᵐ z ∂ρ, P z.1 ∧ (∀ i : Fin 4, P (starSample z.2 i)) ∧
      ∀ i : Fin 4, R z.1 (starSample z.2 i) := by
  let S := conditionalResampling μ state hstate
  letI : IsMarkovKernel S := conditionalResampling_markov μ state hstate
  letI := starKernel_markov S
  have hInv : Kernel.Invariant S μ := conditionalResampling_invariant μ state hstate
  have hdrawP : ∀ᵐ ω ∂μ, ∀ᵐ z ∂S ω, P z := by
    apply Measure.ae_ae_of_ae_comp
    rw [hInv]
    exact hP
  have hdrawR : ∀ᵐ ω ∂μ, ∀ᵐ z ∂S ω, R ω z := by
    filter_upwards [conditionalResampling_ae_key μ state hstate] with ω hω
    filter_upwards [hω] with z hz
    exact hcert ω z hz
  have hstar : ∀ᵐ ω ∂μ, ∀ᵐ z ∂starKernel S ω,
      ∀ i : Fin 4, P (starSample z i) ∧ R ω (starSample z i) := by
    filter_upwards [hdrawP, hdrawR] with ω hp hr
    rw [starKernel_apply]
    exact ae_star_all (S ω) (fun z => P z ∧ R ω z) (hp.and hr)
  have hmeas : MeasurableSet {z : Ω × ((Ω × Ω) × (Ω × Ω)) |
      ∀ i : Fin 4, P (starSample z.2 i) ∧ R z.1 (starSample z.2 i)} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (hPm.preimage ((measurable_starSample i).comp measurable_snd)).inter
      (hR.preimage (measurable_fst.prodMk ((measurable_starSample i).comp measurable_snd)))
  have hAll := Measure.ae_compProd_of_ae_ae hmeas hstar
  have hOld := Measure.ae_compProd_of_ae_fst (starKernel S) hPm hP
  have hfull : ∀ᵐ z ∂(μ ⊗ₘ starKernel S),
      P z.1 ∧ (∀ i : Fin 4, P (starSample z.2 i)) ∧
        ∀ i : Fin 4, R z.1 (starSample z.2 i) := by
    filter_upwards [hAll, hOld] with z hz ho
    exact ⟨ho, fun i => (hz i).1, fun i => (hz i).2⟩
  exact ae_mono Measure.restrict_le_self hfull

end Submission.Lib.K4ScalarActualSwitching
