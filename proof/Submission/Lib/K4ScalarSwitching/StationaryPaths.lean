/-
Adapted from: here:o062
Original proof: session x0212, commit ce4b105,
Submission/Obl/k4_scalar_mesh_projection/StationaryPaths.lean.
-/

import Mathlib

namespace Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- A stationary next-state draw keeps the current marginal dominated by
its unchanged incidence law, even after arbitrary restrictions of the past. -/
theorem stationary_history_snd_le {H Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (θ : Measure H) [SFinite θ] (μ : Measure Ω) [SFinite μ]
    (key : H → Ω) (hkey : Measurable key)
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (hstationary : Kernel.Invariant κ μ)
    (hmarg : θ.map key ≤ μ) :
    (θ ⊗ₘ κ.comap key hkey).snd ≤ μ := by
  rw [Measure.snd_compProd, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map hkey]
  calc
    κ ∘ₘ θ.map key ≤ κ ∘ₘ μ := by
      refine Measure.le_iff.mpr ?_
      intro A hA
      rw [Measure.bind_apply hA κ.aemeasurable, Measure.bind_apply hA κ.aemeasurable]
      exact lintegral_mono' hmarg le_rfl
    _ = μ := hstationary

/-- Short next states are charged to the stationary incidence marginal;
a history-dependent pencil event is charged to its pointwise conditional
ceiling. The entire retained transition remains unnormalized. -/
theorem stationary_history_good_step_ae {H Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (θ : Measure H) [SFinite θ] (μ : Measure Ω) [SFinite μ]
    (key : H → Ω) (hkey : Measurable key)
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (hstationary : Kernel.Invariant κ μ)
    (hmarg : θ.map key ≤ μ)
    (B : Set Ω) (hB : MeasurableSet B)
    (V : Set (H × Ω)) (hV : MeasurableSet V) (p : ENNReal)
    (hpencil : ∀ᵐ h ∂θ, κ (key h) (Prod.mk h ⁻¹' V) ≤ p) :
    let ρ := θ ⊗ₘ κ.comap key hkey
    let Good := {z : H × Ω | z.2 ∉ B ∧ z ∉ V}
    (ρ.restrict Good).snd ≤ μ ∧
      θ univ ≤ (ρ.restrict Good) univ + μ B + p * θ univ := by
  let ρ := θ ⊗ₘ κ.comap key hkey
  let Bad : Set (H × Ω) := (Prod.snd ⁻¹' B) ∪ V
  have hBad : MeasurableSet Bad := (hB.preimage measurable_snd).union hV
  have hshort : ρ (Prod.snd ⁻¹' B) ≤ μ B := by
    have h := Measure.le_iff.mp
      (stationary_history_snd_le θ μ key hkey κ hstationary hmarg) B hB
    rw [Measure.snd_apply hB] at h
    exact h
  have hp : ρ V ≤ p * θ univ := by
    rw [Measure.compProd_apply hV]
    calc
      (∫⁻ h, κ.comap key hkey h (Prod.mk h ⁻¹' V) ∂θ) ≤ ∫⁻ _h, p ∂θ := by
        apply lintegral_mono_ae
        filter_upwards [hpencil] with h hh
        exact hh
      _ = p * θ univ := by simp
  have hbadmass : ρ Bad ≤ μ B + p * θ univ :=
    (measure_union_le _ _).trans (add_le_add hshort hp)
  have hGood : {z : H × Ω | z.2 ∉ B ∧ z ∉ V} = Badᶜ := by
    ext z
    simp only [Bad, mem_ofPred_eq, mem_compl_iff, mem_union, mem_preimage, not_or]
  rw [hGood]
  constructor
  · change Measure.map Prod.snd (ρ.restrict Badᶜ) ≤ μ
    exact (Measure.map_mono Measure.restrict_le_self measurable_snd).trans
      (stationary_history_snd_le θ μ key hkey κ hstationary hmarg)
  · rw [Measure.restrict_apply_univ]
    have htotal : ρ univ = θ univ := Measure.compProd_apply_univ
    calc
      θ univ = ρ Badᶜ + ρ Bad := by rw [← htotal, add_comm, measure_add_measure_compl hBad]
      _ ≤ ρ Badᶜ + (μ B + p * θ univ) := add_le_add le_rfl hbadmass
      _ = ρ Badᶜ + μ B + p * θ univ := by rw [add_assoc]

/-- Pointwise form of the stationary retained-transition budget. -/
theorem stationary_history_good_step {H Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace Ω]
    (θ : Measure H) [SFinite θ] (μ : Measure Ω) [SFinite μ]
    (key : H → Ω) (hkey : Measurable key)
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (hstationary : Kernel.Invariant κ μ)
    (hmarg : θ.map key ≤ μ)
    (B : Set Ω) (hB : MeasurableSet B)
    (V : Set (H × Ω)) (hV : MeasurableSet V) (p : ENNReal)
    (hpencil : ∀ h, κ (key h) (Prod.mk h ⁻¹' V) ≤ p) :
    let ρ := θ ⊗ₘ κ.comap key hkey
    let Good := {z : H × Ω | z.2 ∉ B ∧ z ∉ V}
    (ρ.restrict Good).snd ≤ μ ∧
      θ univ ≤ (ρ.restrict Good) univ + μ B + p * θ univ :=
  stationary_history_good_step_ae θ μ key hkey κ hstationary hmarg B hB V hV p
    (ae_of_all θ hpencil)

end Submission.Lib.K4ScalarSwitching
