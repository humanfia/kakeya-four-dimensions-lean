/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit ed038a4ab9a98a1a195ee216d4f2085211ad55a6,
Submission/Obl/k4_scalar_mesh_projection/RetainedProjection.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.ProjectedPaths

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- Deleting next states from an actual joint transition is exactly
restriction of the transition kernel, with no renormalization. -/
theorem compProd_restrict_next {H Y : Type*}
    [MeasurableSpace H] [MeasurableSpace Y]
    (θ : Measure H) [SFinite θ] (κ : Kernel H Y) [IsSFiniteKernel κ]
    (W : Set Y) (hW : MeasurableSet W) :
    (θ ⊗ₘ κ).restrict (Prod.snd ⁻¹' W) = θ ⊗ₘ κ.restrict hW := by
  ext A hA
  rw [Measure.restrict_apply hA, Measure.compProd_apply hA,
    Measure.compProd_apply (hA.inter (hW.preimage measurable_snd))]
  apply lintegral_congr
  intro h
  rw [Kernel.restrict_apply, Measure.restrict_apply' hW]
  rfl

/-- An arbitrary successful path restriction inherits the conditional
ceiling of the retained next states. The old history and reference law
are kept throughout. -/
theorem retained_projected_history_le {H Z Y C : Type*}
    [MeasurableSpace H] [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableSpace C]
    (θ : Measure H) [SFinite θ] (ν : Measure Z) [SFinite ν]
    (τ : Measure C) [SFinite τ] (κ : Kernel H Y) [IsSFiniteKernel κ]
    (past : H → Z) (hpast : Measurable past)
    (next : Y → C) (hnext : Measurable next)
    (W : Set Y) (hW : MeasurableSet W) (G : Set (H × Y))
    (hG : G ⊆ Prod.snd ⁻¹' W) (K D : ENNReal)
    (hθ : θ.map past ≤ K • ν)
    (hκ : ∀ᵐ h ∂θ, ((κ h).restrict W).map next ≤ D • τ) :
    ((θ ⊗ₘ κ).restrict G).map (Prod.map past next) ≤ (K * D) • ν.prod τ := by
  have hrestriction : (θ ⊗ₘ κ).restrict G ≤ θ ⊗ₘ κ.restrict hW := by
    rw [← compProd_restrict_next θ κ W hW]
    exact Measure.restrict_mono_set _ hG
  have hupper := projected_history_compProd_le_ae θ ν τ (κ.restrict hW)
    past hpast next hnext K D hθ
    (by simpa only [Kernel.restrict_apply] using hκ)
  exact (Measure.map_mono hrestriction (hpast.prodMap hnext)).trans hupper

end Submission.Lib.K4ScalarActualSwitching
