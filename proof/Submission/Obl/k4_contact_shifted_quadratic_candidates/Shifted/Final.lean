import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.Main
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted.FrameExistence
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.ResidualReady

/-!
# Closing the obligation

`Transfer.GoodFrames` (from o243, sessions x0835/x0843) restates this
obligation's `GoodFrames` field by field; `toTransfer` converts. Its
`residualReady` gives `ResidualReady`, frame existence is
`contact_frame_existence`, and `shiftedTransfer_of` assembles the field-named
obligation.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

noncomputable section

/-- The same frames, as the clone of the interface in `Transfer`. -/
def GoodFrames.toTransfer {α : Type} [MeasurableSpace α] {D : Data α} {s₀ U' e₀' : ℝ}
    (gf : GoodFrames D s₀ U' e₀') : Transfer.GoodFrames D s₀ U' e₀' where
  fr := gf.fr
  Rk := gf.Rk
  θ := gf.θ
  K₂ := gf.K₂
  good := gf.good
  rho_floor := gf.rho_floor
  eventually_some := gf.eventually_some
  Rk_large := gf.Rk_large
  θ_large := gf.θ_large
  K₂_small := gf.K₂_small
  H_small := gf.H_small
  gap_small := gf.gap_small
  steps_small := gf.steps_small

namespace Shifted

/-- The residual model on good frames is ready. -/
theorem residualReady : ResidualReady := by
  intro α _ D hcal hD s₀ U' hs₀ hU' hU'4 hκ gf
  have p := hD.parameters
  have he₀' : 0 < (D.e₀ - D.κ * s₀) / 2 := by
    have hκs : D.κ * s₀ ≤ D.κ * (s₀ + U') :=
      mul_le_mul_of_nonneg_left (by linarith) p.rate_pos.le
    have := p.defect_pos
    linarith
  exact Transfer.GoodFrames.residualReady gf.toTransfer p hD.basic hD.caps hcal hs₀ hU' he₀'

/-- The field-named obligation. -/
theorem shiftedTransfer : ShiftedTransfer :=
  shiftedTransfer_of (fun _ _ _ hD => contact_frame_existence hD) residualReady

end Shifted

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
