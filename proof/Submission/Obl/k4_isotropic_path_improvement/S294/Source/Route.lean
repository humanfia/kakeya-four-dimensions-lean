-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.Route, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- o265 from the per-sample producer alone (session x1088).

`Source.Skeleton.relRowCoreNat_of_sample` turns `SampleProducer` into x1080's
`RelRowCoreNatSourceAssertion`; `O204/Tangent/Accepted.lean` turns that, with the accepted o288
and o295, into `StagedWeakAssertion`, definitionally o265's frozen statement. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Skeleton
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Glue
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Accepted

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

/-- **o265 from the per-sample producer.** -/
theorem staged_of_sampleProducer (tune : Tuning) (hS : SampleProducer tune) :
    O204.Split.StagedWeakAssertion :=
  O204.Tangent.staged_of_rel_row_core_nat (relRowCoreNat_of_sample tune hS)

/-- **o265 from the per-sample stages** (`Source.Stages.StagesProducer`): root survivors, then
the cap, state, row and qualification clauses at every dense child. -/
theorem staged_of_stagesProducer (tune : Tuning) (hS : StagesProducer tune) :
    O204.Split.StagedWeakAssertion :=
  staged_of_sampleProducer tune (sampleProducer_of_stages tune hS)

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
