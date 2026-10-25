import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.Assembly
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.Regularization

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

/-- The proposed three analytic children close the exact frozen interior engine. -/
theorem interior_of_chart_inputs (hjet : FirstJet.FirstJetCover)
    (hreg : ChartRegularization) (hraw : RawFirstJetCover → PartialStep) :
    ScalarInput → RowInput → MatchingInput → Base → Interior :=
  interior_of_partial_step (hraw (raw_firstJet_of_regularization hreg hjet))

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
