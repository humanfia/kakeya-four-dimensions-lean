import Submission.Obl.k4_contact_affine_residual_candidate_transfer.RawAdapter
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.Shifted.Complete
import Submission.Obl.k4_contact_regular_quadratic_reconstruction

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Submission.Obl.k4_critical_switching_state_preparation

/-- Prepare a bounded horizontal residual and return its candidates through
the original regular quadratic, retaining the original assignment masses. -/
theorem contactTransfer : ContactTransfer := by
  intro hcal hTC hH α _ cfg hcfg
  have hshift := shiftedTransfer hcal hH α cfg hcfg
  have hp := hcfg.parameters
  exact Submission.k4_contact_regular_quadratic_reconstruction hcal hTC
    cfg.N cfg.K hp.scale hp.scale_limit hp.subpower
    cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀ hp.dimension_nonneg hp.dimension_lt_one
    hp.rate_pos hp.rate_le_one hp.transverse_pos (by rw [hcfg.equal_rates])
    hp.palette_pos hp.palette_le_one hp.depth_pos hp.defect_pos trivial
    (fun _ => hcfg.equal_rates) α
    cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n cfg.j cfg.A cfg.B cfg.c cfg.F
    hcfg.contact hcfg.basic hcfg.caps hcfg.atlas hcfg.nested hcfg.equal_rates hshift

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
