import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.Main
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.FrameExistence
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ResidualReady

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Submission.Obl.k4_critical_switching_state_preparation

/-- Simultaneous affine palettes and the horizontal principle give candidates
in bounded shifted coordinates, with the original assignment weights. -/
theorem shiftedTransfer : ShiftedTransfer := by
  apply Shifted.shiftedTransfer_of
  · intro α _ D hD
    exact contact_frame_existence hD
  · intro α _ D hcal hD s₀ U' hs₀ hU' _ hmargin gf
    have hκ : 0 < D.κ := hD.parameters.rate_pos
    have he₀ : 0 < D.e₀ := hD.parameters.defect_pos
    have hmul : 0 < D.κ * U' := mul_pos hκ hU'
    have he' : 0 < (D.e₀ - D.κ * s₀) / 2 := by
      nlinarith only [hmargin, he₀, hmul]
    exact gf.residualReady hD.parameters hD.basic hD.caps hcal hs₀ hU' he'

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
