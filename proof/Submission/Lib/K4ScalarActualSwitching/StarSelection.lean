/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 2e65ac82f715df53d854782d6e862452630b9dde,
Submission/Obl/k4_scalar_mesh_projection/StarSelection.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.Resampling

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

def starSample {Ω : Type*} (z : (Ω × Ω) × (Ω × Ω)) : Fin 4 → Ω :=
  ![z.1.1, z.1.2, z.2.1, z.2.2]

def starPair {Ω : Type*} (i : Fin 6) (z : (Ω × Ω) × (Ω × Ω)) : Ω × Ω :=
  ![(z.1.1, z.1.2), (z.1.1, z.2.1), (z.1.1, z.2.2),
    (z.1.2, z.2.1), (z.1.2, z.2.2), (z.2.1, z.2.2)] i

theorem measurable_starPair {Ω : Type*} [MeasurableSpace Ω] (i : Fin 6) :
    Measurable (starPair (Ω := Ω) i) := by
  fin_cases i
  · exact measurable_fst
  · exact measurable_fst.prodMap measurable_fst
  · exact measurable_fst.prodMap measurable_snd
  · exact measurable_snd.prodMap measurable_fst
  · exact measurable_snd.prodMap measurable_snd
  · exact measurable_snd

theorem measurePreserving_starPair {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (i : Fin 6) :
    MeasurePreserving (starPair i) ((ν.prod ν).prod (ν.prod ν)) (ν.prod ν) := by
  fin_cases i
  · exact measurePreserving_fst
  · exact (measurePreserving_fst (μ := ν) (ν := ν)).prod
      (measurePreserving_fst (μ := ν) (ν := ν))
  · exact (measurePreserving_fst (μ := ν) (ν := ν)).prod
      (measurePreserving_snd (μ := ν) (ν := ν))
  · exact (measurePreserving_snd (μ := ν) (ν := ν)).prod
      (measurePreserving_fst (μ := ν) (ν := ν))
  · exact (measurePreserving_snd (μ := ν) (ν := ν)).prod
      (measurePreserving_snd (μ := ν) (ν := ν))
  · exact measurePreserving_snd

def controlPencil {Ω : Type*} (control : Ω → ℝ) (r : ℝ) : Set (Ω × Ω) :=
  {z | |control z.1 - control z.2| < r}

theorem measurableSet_controlPencil {Ω : Type*} [MeasurableSpace Ω]
    (control : Ω → ℝ) (hcontrol : Measurable control) (r : ℝ) :
    MeasurableSet (controlPencil control r) :=
  measurableSet_lt ((hcontrol.comp measurable_fst).sub (hcontrol.comp measurable_snd)).abs
    measurable_const

/-- One palette ceiling controls an independent pair's thin-pencil
probability. Only the first variable is integrated against a probability. -/
theorem pair_pencil_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (control : Ω → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) (K p : ENNReal) (r : ℝ)
    (hpalette : ν.map control ≤ K • π)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p) :
    (ν.prod ν) (controlPencil control r) ≤ K * p := by
  rw [Measure.prod_apply (measurableSet_controlPencil control hcontrol r)]
  calc
    _ ≤ ∫⁻ _ : Ω, K * p ∂ν := by
      apply lintegral_mono
      intro x
      have hA : MeasurableSet {v : ℝ | |v - control x| < r} :=
        measurableSet_lt (measurable_id.sub measurable_const).abs measurable_const
      have heq : Prod.mk x ⁻¹' controlPencil control r =
          control ⁻¹' {v : ℝ | |v - control x| < r} := by
        ext y
        simp [controlPencil, abs_sub_comm]
      change ν (Prod.mk x ⁻¹' controlPencil control r) ≤ K * p
      rw [heq, ← Measure.map_apply hcontrol hA]
      apply (Measure.le_iff.mp hpalette _ hA).trans
      rw [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl (hthin (control x))
    _ = K * p := by simp

def starBad {Ω : Type*} (control : Ω → ℝ) (r : ℝ) : Set ((Ω × Ω) × (Ω × Ω)) :=
  ⋃ i : Fin 6, starPair i ⁻¹' controlPencil control r

theorem measurableSet_starBad {Ω : Type*} [MeasurableSpace Ω]
    (control : Ω → ℝ) (hcontrol : Measurable control) (r : ℝ) :
    MeasurableSet (starBad control r) :=
  MeasurableSet.iUnion fun i =>
    (measurableSet_controlPencil control hcontrol r).preimage (measurable_starPair i)

theorem four_sample_pencil_mass_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (control : Ω → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) (K p : ENNReal) (r : ℝ)
    (hpalette : ν.map control ≤ K • π)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p) :
    ((ν.prod ν).prod (ν.prod ν)) (starBad control r) ≤ 6 * (K * p) := by
  calc
    _ ≤ ∑ i : Fin 6,
        ((ν.prod ν).prod (ν.prod ν)) (starPair i ⁻¹' controlPencil control r) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin 6, K * p := by
      apply Finset.sum_le_sum
      intro i _
      have hmp := measurePreserving_starPair ν i
      rw [← Measure.map_apply hmp.measurable (measurableSet_controlPencil control hcontrol r), hmp.map_eq]
      exact pair_pencil_mass_le ν control hcontrol π K p r hpalette hthin
    _ = 6 * (K * p) := by simp [nsmul_eq_mul]

noncomputable def starKernel {Ω : Type*} [MeasurableSpace Ω] (S : Kernel Ω Ω) :
    Kernel Ω ((Ω × Ω) × (Ω × Ω)) := (S ×ₖ S) ×ₖ (S ×ₖ S)

theorem starKernel_markov {Ω : Type*} [MeasurableSpace Ω]
    (S : Kernel Ω Ω) [IsMarkovKernel S] : IsMarkovKernel (starKernel S) := by
  unfold starKernel
  infer_instance

theorem starKernel_apply {Ω : Type*} [MeasurableSpace Ω]
    (S : Kernel Ω Ω) [IsMarkovKernel S] (ω : Ω) :
    starKernel S ω = ((S ω).prod (S ω)).prod ((S ω).prod (S ω)) := by
  simp only [starKernel, Kernel.prod_apply]

/-- Four line draws at the same actual state retain the original start
reference and lose at most the six thin-pair budgets. -/
theorem star_retained_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (S : Kernel Ω Ω) [IsMarkovKernel S]
    (control : Ω → ℝ) (hcontrol : Measurable control)
    (π : Measure ℝ) (K p : ENNReal) (r : ℝ)
    (hpalette : ∀ᵐ ω ∂μ, (S ω).map control ≤ K • π)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p) :
    let θ := μ ⊗ₘ starKernel S
    let ρ := θ.restrict (Prod.snd ⁻¹' (starBad control r)ᶜ)
    ρ.fst ≤ μ ∧ μ univ ≤ ρ univ + (6 * (K * p)) * μ univ := by
  letI := starKernel_markov S
  let θ := μ ⊗ₘ starKernel S
  let B : Set (Ω × ((Ω × Ω) × (Ω × Ω))) := Prod.snd ⁻¹' starBad control r
  have hB : MeasurableSet B := (measurableSet_starBad control hcontrol r).preimage measurable_snd
  have hbad : θ B ≤ (6 * (K * p)) * μ univ := by
    rw [Measure.compProd_apply hB]
    calc
      _ ≤ ∫⁻ _ : Ω, 6 * (K * p) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hpalette] with ω hω
        change starKernel S ω (starBad control r) ≤ 6 * (K * p)
        rw [starKernel_apply]
        exact four_sample_pencil_mass_le (S ω) control hcontrol π K p r hω hthin
      _ = (6 * (K * p)) * μ univ := by simp
  have hcompl : Prod.snd ⁻¹' (starBad control r)ᶜ = Bᶜ := rfl
  rw [hcompl]
  refine ⟨(Measure.fst_mono Measure.restrict_le_self).trans_eq (Measure.fst_compProd _ _), ?_⟩
  rw [Measure.restrict_apply_univ]
  calc
    μ univ = θ Bᶜ + θ B := by
      rw [add_comm, measure_add_measure_compl hB]
      exact Measure.compProd_apply_univ.symm
    _ ≤ θ Bᶜ + (6 * (K * p)) * μ univ := add_le_add le_rfl hbad

end Submission.Lib.K4ScalarActualSwitching
