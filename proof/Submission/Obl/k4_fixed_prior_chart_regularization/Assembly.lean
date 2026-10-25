import Submission.Obl.k4_fixed_prior_chart_regularization.Frozen
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.LocalStage
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.RowStage
import Submission.Obl.k4_fixed_prior_chart_regularization.Reg.BinStage

namespace Submission.Obl.k4_fixed_prior_chart_regularization

/-- All stages except the slope selection are assembled here. -/
theorem statement_of_stageSlope (hSlope : Reg.StageSlope) : Statement :=
  statement_of_chartRegularization
    (Reg.chartRegularization_of_stages Reg.stageLocal Reg.stageRow hSlope Reg.stageBin)

end Submission.Obl.k4_fixed_prior_chart_regularization
