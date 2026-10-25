import Submission.Obl.k4_scalar_initial_true_horizon.SplitInterface
import Submission.Obl.k4_scalar_true_atlas_terminal_lists

namespace Submission.Obl.k4_scalar_initial_true_horizon

/-- The accepted terminal-list theorem leaves exactly the raw initial atlas
construction to prove the frozen initial-horizon statement. -/
theorem initial_of_raw (hraw : RawInitial) : Initial :=
  initial_of_raw_recovery hraw Submission.k4_scalar_true_atlas_terminal_lists

end Submission.Obl.k4_scalar_initial_true_horizon
