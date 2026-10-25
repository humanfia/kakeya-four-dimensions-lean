/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/SelectedMaskMonotonicity.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SubmeasurePaths

/-! Later common masks give smaller laws in every unchanged original
world, including original worlds with zero mixture weight. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem selectedWorldLaw_mono_mask {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    {A B : Set (Fin (W z k) × State)} (hAB : A ⊆ B) (g : Fin (W p (chain.sample k))) :
    chain.selectedWorldLaw k A g ≤ chain.selectedWorldLaw k B g := by
  have hmap : chain.selectedLaw k A ≤ chain.selectedLaw k B :=
    chain.submeasureLaw_mono k (Measure.restrict_mono hAB le_rfl)
  apply Measure.le_iff.mpr
  intro S _
  simp only [selectedWorldLaw, originalFibers, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl ((worldFiber_mono hmap g) S)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
