/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit ed038a4ab9a98a1a195ee216d4f2085211ad55a6,
Submission/Obl/k4_scalar_mesh_projection/PaletteConditioning.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.Resampling

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Rectangular caps relative to the unchanged mass of each discrete
state give the actual conditional palette ceiling. Zero-mass states are
discarded only as a null set for the original incidence law. -/
theorem condDistrib_palette_le {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (hcontrol : Measurable control)
    (π : Measure V) (K : ENNReal)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {ω | state ω = q ∧ control ω ∈ A} ≤ K * μ (state ⁻¹' {q}) * π A) :
    ∀ᵐ q ∂μ.map state, condDistrib control state μ q ≤ K • π := by
  apply ae_iff_of_countable.mpr
  intro q hq
  refine Measure.le_iff.mpr ?_
  intro A hA
  rw [condDistrib_apply_of_ne_zero hstate hcontrol q hq A,
    Measure.map_apply (hstate.prodMk hcontrol) ((measurableSet_singleton q).prod hA),
    Measure.map_apply hstate (measurableSet_singleton q)]
  have heq : (fun ω => (state ω, control ω)) ⁻¹' ({q} ×ˢ A) =
      {ω | state ω = q ∧ control ω ∈ A} := by
    ext ω
    simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_ofPred_eq]
  rw [heq, Measure.smul_apply, smul_eq_mul]
  have hmass : μ (state ⁻¹' {q}) ≠ 0 := by
    rwa [Measure.map_apply hstate (measurableSet_singleton q)] at hq
  calc
    _ ≤ (μ (state ⁻¹' {q}))⁻¹ * (K * μ (state ⁻¹' {q}) * π A) :=
      mul_le_mul' le_rfl (hcap q A hA)
    _ = K * π A := by
      rw [show K * μ (state ⁻¹' {q}) * π A = μ (state ⁻¹' {q}) * (K * π A) by ac_rfl,
        ← mul_assoc, ENNReal.inv_mul_cancel hmass (measure_ne_top _ _), one_mul]

/-- The rectangular cap gives the palette bound for the literal
full-incidence conditional redraw used in the switched experiment. -/
theorem conditionalResampling_palette_le {Ω Q V : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (hcontrol : Measurable control)
    (π : Measure V) (K : ENNReal)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {ω | state ω = q ∧ control ω ∈ A} ≤ K * μ (state ⁻¹' {q}) * π A) :
    ∀ᵐ ω ∂μ, (conditionalResampling μ state hstate ω).map control ≤ K • π := by
  have hq : ∀ᵐ q ∂μ.map state,
      ((condDistrib (id : Ω → Ω) state μ).map control) q ≤ K • π := by
    filter_upwards [condDistrib_palette_le μ state hstate control hcontrol π K hcap,
      condDistrib_comp hstate.aemeasurable (aemeasurable_id : AEMeasurable (id : Ω → Ω) μ)
        hcontrol] with q hq heq
    rw [← heq]
    exact hq
  have hω := ae_of_ae_map hstate.aemeasurable hq
  filter_upwards [hω] with ω hω
  simpa only [conditionalResampling, Kernel.comap_apply, Kernel.map_apply _ hcontrol] using hω

end Submission.Lib.K4ScalarActualSwitching
