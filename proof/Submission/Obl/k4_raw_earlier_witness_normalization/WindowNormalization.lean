import Submission.Obl.k4_raw_earlier_witness_normalization.Assembly
import Submission.Obl.k4_raw_earlier_witness_normalization.Window

namespace Submission.Obl.k4_raw_earlier_witness_normalization

/-- The explicit strip comparison supplies normalized scalar-window proximity. -/
theorem window_normalization : WindowNormalization := by
  intro N χ s m t₀ q B c u n center velocity D thickness p p' hN hn hth hstrip hstrip' ht hy hframe hnormal
  exact window_proximity N m s χ hN t₀ q B c u D rawPlanar normalTangent (fun _ => rfl)
    baseProjection (fun _ => rfl) (earlierCoordinates t₀ q B c u D) (fun _ => rfl)
    n center velocity thickness 0 hn hframe hnormal p p' (p 0) (p' 0)
    (inner ℝ (normalTangent n) (rawPlanar p))
    (inner ℝ (normalTangent n) (rawPlanar p'))
    rfl rfl (by simp) (by simp) hstrip hstrip' ht hy

end Submission.Obl.k4_raw_earlier_witness_normalization
