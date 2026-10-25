/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/GoodFramesResidual.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.GoodFramesAtlas
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FrameCapsAt

/-!
# The residual atlas on good frames, from the original model

The residual caps of good frames come from the original basic bounds and mesh
caps (`eventual_frame_capsAt`), so the residual atlas on good frames needs only
the original model, the mesh calibration constant and a loss sequence above the
atlas constant.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ}

theorem frameCapsEventually (p : Parameters D) (h1 : D.Basic) (h2 : D.Caps) (hs₀ : 0 ≤ s₀)
    (hU' : 0 < U') : FrameCapsEventually D s₀ U' (9 * U' + 2) :=
  eventual_frame_capsAt D p h1 h2 (by linarith) hs₀

/-- The residual atlas on good frames, for every loss sequence eventually above
the atlas constant. -/
theorem GoodFrames.residual_atlas_of_model (gf : GoodFrames D s₀ U' e₀') (p : Parameters D)
    (h1 : D.Basic) (h2 : D.Caps) (hs₀ : 0 < s₀) (hU' : 0 < U') {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hA : BoxCalibration A₀) (K' : ℕ → ℝ) (hK' : ∀ᶠ k in atTop, gf.atlasK A₀ k ≤ K' k) :
    (residualData D s₀ U' e₀' K' gf.fr).Atlas :=
  gf.residual_atlas p hs₀ hU' hA₀ hA (frameCapsEventually p h1 h2 hs₀.le hU') K' hK'

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
