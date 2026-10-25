/- Adapted from this LOT tree, o197, session x0690, Pairing/LabelBadMass.lean (o197 branch
   x0690, refs/merged/o197/x0690), itself adapted from o178, session x0596, commit
   aff0309c5b5be9920172fe7e367c31d64a3a01e3, LabelBadMass.lean: only the coarsening
   measurability and the zero-depth coarsening identity are kept here. -/
import Submission.Obl.k4_raw_localized_native_systems.Pairing.ProblemDensities
import Submission.Lib.K4XInterface.Basic

namespace Submission.Obl.k4_raw_localized_native_systems.Pairing

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

theorem measurable_coarsenObs (n : ℕ) :
    Measurable (Submission.Lib.K4XInterface.coarsenObs n) := by
  unfold Submission.Lib.K4XInterface.coarsenObs
  exact measurable_fst.prodMk
    ((measurable_of_countable (fun z : ℤ => z / (2 : ℤ) ^ n)).comp measurable_snd)

/-- The depth-zero observation is a coarsening of the terminal one. -/
theorem obs_zero_eq_coarsen {N L : ℝ} (hN : 1 ≤ N) (hL : 0 ≤ L) (B : ℝ) (q : Point) :
    obs B (δ N 0) q = Submission.Lib.K4XInterface.coarsenObs
      (Submission.Lib.K4XInterface.depthIdx N L - Submission.Lib.K4XInterface.depthIdx N 0)
      (obs B (δ N L) q) :=
  Submission.Lib.K4XInterface.gobs_coarsen hN le_rfl hL B q

end
end Submission.Obl.k4_raw_localized_native_systems.Pairing
