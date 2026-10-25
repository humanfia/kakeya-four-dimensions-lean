/-
Adapted from: here:o062
Original proof: x0212, commit 1620a3a.
Owned source: Submission/Obl/k4_scalar_mesh_projection/LineRefresh.lean.
-/

import Mathlib

/-! Explicit line-preserving endpoint refresh for a disintegrated incidence law. -/

namespace Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable def lineRefreshKernel {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (κ : Kernel X T) :
    Kernel (X × T) (X × T) :=
  (Kernel.id ×ₖ κ).comap Prod.fst measurable_fst

theorem lineRefreshKernel_apply {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (κ : Kernel X T) [IsSFiniteKernel κ]
    (ω : X × T) :
    lineRefreshKernel κ ω = Measure.map (Prod.mk ω.1) (κ ω.1) := by
  rw [lineRefreshKernel, Kernel.comap_apply, Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod]

theorem lineRefreshKernel_markov {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T] (κ : Kernel X T) [IsMarkovKernel κ] :
    IsMarkovKernel (lineRefreshKernel κ) := by
  unfold lineRefreshKernel
  infer_instance

/-- Refreshing time while retaining the sampled line preserves the full
original incidence law, before any duration or geometric pruning. -/
theorem lineRefreshKernel_invariant {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (κ : Kernel X T) [IsMarkovKernel κ] :
    Kernel.Invariant (lineRefreshKernel κ) (ν ⊗ₘ κ) := by
  change lineRefreshKernel κ ∘ₘ (ν ⊗ₘ κ) = ν ⊗ₘ κ
  rw [lineRefreshKernel, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map measurable_fst]
  change (Kernel.id ×ₖ κ) ∘ₘ (ν ⊗ₘ κ).fst = ν ⊗ₘ κ
  rw [Measure.fst_compProd, ← Measure.compProd_eq_comp_prod]

theorem lineRefreshKernel_ae_line {X T : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace T]
    (κ : Kernel X T) [IsSFiniteKernel κ] (ω : X × T) :
    ∀ᵐ ω' ∂lineRefreshKernel κ ω, ω'.1 = ω.1 := by
  rw [lineRefreshKernel_apply]
  apply (ae_map_iff measurable_prodMk_left.aemeasurable
    ((measurableSet_singleton ω.1).preimage measurable_fst)).mpr
  exact ae_of_all _ (fun _ => rfl)

end Submission.Lib.K4ScalarSwitching
