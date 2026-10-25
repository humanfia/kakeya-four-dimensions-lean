import Submission.Obl.k4_horizontal_endpoint_three_projections.Expanded
import Submission.Obl.k4_horizontal_endpoint_three_projections.PairedInterface
import Submission.Obl.k4_horizontal_endpoint_three_projections.SplitDepths

namespace Submission.Obl.k4_horizontal_endpoint_three_projections

open MeasureTheory Set Filter

/-- The grid precedes the universal endpoint call. The coarse and terminal
depths follow its returned range; the output coefficient exponent precedes losses. -/
theorem projection_of_split
    (hpair : Matching → PairedComparison)
    (hcharts : CorrectedCharts)
    (hreturn : Scalar → ScalarReturn) :
    Scalar → Matching → EndpointEngine → ProjectionEngine := by
  intro hScalar hMatching hEngine α inst cfg hp buffer hbuffer
  obtain ⟨M, hM, hMe, hMU, hMeBuffer⟩ :=
    exists_projection_mesh hp.depth_pos hp.defect_pos (by linarith : 0 < buffer)
  obtain ⟨sMax, RE, hEndpoint⟩ :=
    (Data.endpoint_iff_exists_with (Data.withDefect cfg M)).mp
      (endpoint_at_smaller_defect hEngine hp hM hMe.le)
  have hsMaxU : 2 * sMax < cfg.U := hEndpoint.2.1
  obtain ⟨s₀, s, u, v, hs₀, hsMax, hbufferM, h100M, hs, hu, hv, hvu,
    hvgain, hsU, hsupper, hwide₁, hwide₂, hdepth⟩ :=
    exists_split_depths hp.dimension_nonneg hp.dimension_lt_one hp.rate_pos
      hp.subcritical_rate hEndpoint.1 hsMaxU hM (by linarith : 0 < buffer)
  have hs₀U : 3 * s₀ / 2 < cfg.U := by linarith [hEndpoint.1]
  have hpaired := hpair hMatching α cfg hp M sMax RE s₀ hM hMe
    hEndpoint hs₀ hsMax h100M
  have hready := hcharts α cfg hp M RE s₀ hM hMe hs₀ hs₀U h100M
    hpaired ![s, s + u, s + v] hdepth
  obtain ⟨R, hR, hprojected⟩ := hreturn hScalar α cfg hp M s₀ s u v hM hMe
    hs₀ h100M hs hu hv hvu hsupper hsU hdepth hready
  have hM_U : M < cfg.U := by nlinarith [mul_pos hM (show 0 < buffer - 1 by linarith)]
  exact ⟨s₀, s, u, v, R, hs₀, hbufferM.trans hM_U, hbufferM.trans hMe,
    hs, hu, hv, hvu, hvgain, hsU, hsupper, hwide₁, hwide₂, hR,
    M, hbufferM, hMU, hMeBuffer, hprojected⟩

end Submission.Obl.k4_horizontal_endpoint_three_projections
