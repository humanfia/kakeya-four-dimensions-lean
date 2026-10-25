import Submission.Obl.k4_raw_critical_segment_forests.PreparedNormalization
import Submission.Obl.k4_remainder_angular_cap_transport.Assemble

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter

/-- The accepted angular transport completes every pure normalized remainder. -/
theorem pureCompletion : PureCompletion := by
  intro p hp M D r h cap s v hr hrL
  apply (k4_remainder_pure_profile_normalization.Data.valid_iff_pure_angular _).mpr
  refine ⟨v.valid, ?_⟩
  exact k4_remainder_angular_cap_transport.transport
    p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G
    ((p.valid_iff_pure_angular).mp hp) r h cap hr hrL M D s.index
    (fun n => (s.atlas n).κ) (fun n => (s.atlas n).T) (fun n => (s.atlas n).C)
    (fun n => (s.atlas n).γ) (fun n => (s.atlas n).j) (fun n => (s.atlas n).c)
    (fun n => (s.atlas n).u) (fun n => (s.atlas n).Q) (fun n => (s.atlas n).R)
    (fun n => (s.atlas n).A) (fun n => (s.atlas n).F) v.K v.E v.f v.g v.G
    ⟨s.strictMono, s.slack_one, s.slack_ambient, s.slack_subpower, s.time_upper, s.valid⟩
    ⟨v.valid, v.event_subset, v.prior_positive, v.normalizer_subpower, v.terminal_comparison⟩

/-- Concrete normalization through supplied prepared parent charts. -/
theorem nestedNormalizationPrepared : NestedNormalizationPrepared :=
  nestedNormalizationPrepared_of_pureCompletion pureCompletion

end Submission.Obl.k4_raw_critical_segment_forests
