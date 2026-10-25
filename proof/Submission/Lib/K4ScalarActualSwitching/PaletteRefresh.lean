/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit cc2047f27dc5dfb9bdb573298de763f228dafc6c,
Submission/Obl/k4_scalar_mesh_projection/PaletteRefresh.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.LineRefresh

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- An endpoint-time refresh preserves the sampled line exactly at the
kernel level, including values at histories outside the incidence support. -/
theorem lineRefreshKernel_map_line {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (κ : Kernel X T) [IsMarkovKernel κ] :
    (lineRefreshKernel κ).map Prod.fst = Kernel.deterministic Prod.fst measurable_fst := by
  rw [lineRefreshKernel, ← Kernel.comap_map_comm _ measurable_fst measurable_fst,
    ← Kernel.fst_eq, Kernel.fst_prod, Kernel.id_comap]

/-- The full refresh after a state-selected line draw has exactly the same
control law as that line draw. Thus conditional pencil ceilings survive the
time refresh for every complete past history. -/
theorem refreshed_control_kernel {H X T C : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T] [MeasurableSpace C]
    (S : Kernel H (X × T)) (κ : Kernel X T) [IsMarkovKernel κ]
    (control : X → C) (hcontrol : Measurable control) :
    (lineRefreshKernel κ ∘ₖ S).map (fun z => control z.1) =
      S.map (fun z => control z.1) := by
  have hmap : (lineRefreshKernel κ).map (fun z => control z.1) =
      Kernel.deterministic (fun z => control z.1) (hcontrol.comp (f := (Prod.fst : X × T → X)) measurable_fst) := by
    change (lineRefreshKernel κ).map (control ∘ Prod.fst) =
      Kernel.deterministic (control ∘ Prod.fst) (hcontrol.comp (f := (Prod.fst : X × T → X)) measurable_fst)
    rw [Kernel.map_comp_right _ measurable_fst hcontrol, lineRefreshKernel_map_line,
      Kernel.deterministic_map measurable_fst hcontrol]
  rw [Kernel.map_comp, hmap, Kernel.deterministic_comp_eq_map]

/-- A prepared palette bound and a uniform thin-pencil cap give the actual
conditional pencil bound after the complete state-and-time switch. The
conditioning history can be arbitrary, and its cap is only required a.e. -/
theorem refreshed_pencil_bound {H X T : Type*}
    [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace T]
    (θ : Measure H) (S : Kernel H (X × T))
    (κ : Kernel X T) [IsMarkovKernel κ]
    (control : X → ℝ) (hcontrol : Measurable control)
    (old : H → ℝ) (π : Measure ℝ) (K p : ENNReal) (r : ℝ)
    (hpalette : ∀ᵐ h ∂θ, (S h).map (fun z => control z.1) ≤ K • π)
    (hthin : ∀ w : ℝ, π {v | |v - w| < r} ≤ p) :
    ∀ᵐ h ∂θ, (lineRefreshKernel κ ∘ₖ S) h
      {z | |control z.1 - old h| < r} ≤ K * p := by
  let transition := lineRefreshKernel κ ∘ₖ S
  let f : X × T → ℝ := fun z => control z.1
  have hf : Measurable f :=
    hcontrol.comp (f := (Prod.fst : X × T → X)) measurable_fst
  have heq : transition.map f = S.map f := refreshed_control_kernel S κ control hcontrol
  filter_upwards [hpalette] with h hh
  have hA : MeasurableSet {v : ℝ | |v - old h| < r} :=
    measurableSet_lt (measurable_id.sub measurable_const).abs measurable_const
  have hmapped : (transition h).map f = (S h).map f :=
    (Kernel.map_apply transition hf h).symm.trans
      ((congrArg (fun L : Kernel H ℝ => L h) heq).trans (Kernel.map_apply S hf h))
  change transition h (f ⁻¹' {v : ℝ | |v - old h| < r}) ≤ K * p
  rw [← Measure.map_apply hf hA, hmapped]
  apply (Measure.le_iff.mp hh _ hA).trans
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (hthin (old h))

end Submission.Lib.K4ScalarActualSwitching
