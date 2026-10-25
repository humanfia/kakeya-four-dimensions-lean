/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 529218036216c5ecc4d0ae32e085d5c07afe48c8,
Submission/Obl/k4_scalar_mesh_projection/RestrictedRefresh.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarSwitching.LineRefresh
import Submission.Lib.K4ScalarSwitching.PathDomination

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Refreshing time mixes the original line marginal with its time kernel. -/
theorem lineRefresh_comp_measure {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (θ : Measure (X × T)) [SFinite θ]
    (κ : Kernel X T) [IsSFiniteKernel κ] :
    lineRefreshKernel κ ∘ₘ θ = θ.fst ⊗ₘ κ := by
  rw [lineRefreshKernel, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map measurable_fst]
  exact (Measure.compProd_eq_comp_prod θ.fst κ).symm

/-- A whole-line restriction can be made before or after refreshing time. -/
theorem compProd_restrict_lines {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (θ : Measure X) [SFinite θ] (κ : Kernel X T) [IsSFiniteKernel κ]
    (L : Set X) (hL : MeasurableSet L) :
    (θ ⊗ₘ κ).restrict (Prod.fst ⁻¹' L) = θ.restrict L ⊗ₘ κ := by
  ext A hA
  rw [Measure.restrict_apply hA,
    Measure.compProd_apply (hA.inter (hL.preimage measurable_fst)),
    Measure.compProd_apply hA]
  rw [← lintegral_indicator hL]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ L
  · simp only [preimage_inter, preimage_preimage,
      Set.indicator_of_mem hx]
    congr 1
    ext t
    simp only [mem_preimage, mem_inter_iff, hx, and_true]
  · rw [Set.indicator_of_notMem hx]
    have hempty : Prod.mk x ⁻¹' (A ∩ Prod.fst ⁻¹' L) = ∅ := by
      ext t
      simp only [mem_preimage, mem_inter_iff, hx, and_false, mem_empty_iff_false]
    rw [hempty, measure_empty]

/-- An a.e. time ceiling suffices for the actual joint control/time law. -/
theorem joint_control_time_transition_le_ae {X C T : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace T]
    (θ : Measure X) [SFinite θ] (π : Measure C) [SFinite π]
    (τ : Measure T) [SFinite τ] (κ : Kernel X T) [IsSFiniteKernel κ]
    (control : X → C) (hcontrol : Measurable control) (K D : ENNReal)
    (hpalette : Measure.map control θ ≤ K • π)
    (hκ : ∀ᵐ x ∂θ, κ x ≤ D • τ) :
    Measure.map (Prod.map control id) (θ ⊗ₘ κ) ≤ (K * D) • π.prod τ := by
  have hprod : θ ⊗ₘ κ ≤ D • θ.prod τ := by
    simpa only [one_mul] using
      history_compProd_le_ae θ θ τ κ 1 D (by simp) hκ
  have hmap := Measure.map_mono hprod (hcontrol.prodMap measurable_id)
  rw [Measure.map_smul D (hcontrol.prodMap measurable_id).aemeasurable] at hmap
  have heq : Measure.map (Prod.map control id) (θ.prod τ) =
      (Measure.map control θ).prod τ := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map θ τ hcontrol measurable_id).symm
  rw [heq] at hmap
  have hp := Measure.prod_mono hpalette (le_refl τ)
  rw [Measure.prod_smul_left K] at hp
  calc
    Measure.map (Prod.map control id) (θ ⊗ₘ κ) ≤
        D • (Measure.map control θ).prod τ := hmap
    _ ≤ D • (K • π.prod τ) := smul_le_smul_left D hp
    _ = (K * D) • π.prod τ := by rw [smul_smul, mul_comm D K]

/-- The original state-selected line draw followed by a time refresh,
restricted to long rows, has the product palette/time ceiling. The row
ceiling is required only on those rows and only almost everywhere. -/
theorem restricted_lineRefresh_control_time_le {X C T : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSpace T]
    (θ : Measure (X × T)) [SFinite θ]
    (π : Measure C) [SFinite π] (τ : Measure T) [SFinite τ]
    (κ : Kernel X T) [IsSFiniteKernel κ]
    (control : X → C) (hcontrol : Measurable control)
    (L : Set X) (hL : MeasurableSet L) (K D : ENNReal)
    (hpalette : θ.map (fun z => control z.1) ≤ K • π)
    (hκ : ∀ᵐ x ∂θ.fst, x ∈ L → κ x ≤ D • τ) :
    Measure.map (Prod.map control id)
      ((lineRefreshKernel κ ∘ₘ θ).restrict (Prod.fst ⁻¹' L)) ≤
        (K * D) • π.prod τ := by
  rw [lineRefresh_comp_measure, compProd_restrict_lines θ.fst κ L hL]
  apply joint_control_time_transition_le_ae (θ.fst.restrict L) π τ κ
    control hcontrol K D
  · apply (Measure.map_mono Measure.restrict_le_self hcontrol).trans
    have heq : θ.fst.map control = θ.map (fun z => control z.1) := by
      rw [Measure.fst, Measure.map_map hcontrol measurable_fst]
      rfl
    rw [heq]
    exact hpalette
  · exact (ae_restrict_iff' hL).mpr hκ

end Submission.Lib.K4ScalarActualSwitching
