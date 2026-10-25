import Submission.Lib.K4ExactProblemOps.Defs
import Submission.Lib.K4ExactProblemOps.FiberSum
import Submission.Lib.K4ExactProblemOps.AngularCoarsening
import Submission.Lib.K4ExactProblemOps.Transfer
import Submission.Lib.K4ExactProblemOps.Coarsening
import Submission.Lib.K4ExactProblemOps.Reindex
import Submission.Lib.K4ExactProblemOps.Rescale
import Submission.Lib.K4ExactProblemOps.Horizon
import Submission.Lib.K4ExactProblemOps.CapDepth

/-!
# Operations on the frozen exact problems

For the frozen `prob`/`term`/`H` of o105 and its descendants:

* `prob_coarsen`: a valid problem of length `L` whose profile has an endpoint cap
  `d' < 1` at `0 < b ≤ L` is a valid problem of length `b` (paper Lemma 2.7); the
  new joint angular density is `fiberSumJ (dsteps (N k) b L) (G k γ u)`.
* `prob_reindex`, `term_of_term_reindex`, `H_shift`: subsequences and index shifts.
* `prob_rescale`, `term_rescale_iff`, `H_rescale`: base change `N ↦ N ^ c`, which
  divides depths, horizons and exponents by `c`; `prob_unit_length`: every valid
  problem has a valid length-one version with horizon `H / L`.
* `chart_transfer`, `fmt_mono`: charts under growth of the polynomial bound.
* `InitialHorizonBound`, `term_nonneg`, `term_mono`, `H_nonneg`, `H_le_of_term`,
  `term_of_H_lt`, `H_le_of_IH`; `term_of_nt`, `H_le_of_nt`, `nt_mono`, `nt_zero_of_term`
  (`|det Q| 4^T ≤ κ²` from `‖Q‖ ≤ κ / 2^T`).
* `exists_cap_depth`, `exists_capped_coarsening`, `term_at_capped_depth`: a nearly
  linear relative profile has, just below any target depth, a tilted-minimizer depth
  with endpoint cap `ds + δ < 1`; the coarsening there is valid, so the frozen initial
  horizon bound gives true systems at that depth at every horizon above it.

The frozen predicates are in `Defs.lean`; statements written with the immediately
applied lambdas of the frozen types unfold to them by `rfl`.

Adapted from: here:o120
(the named frozen predicates in `Defs.lean` follow x0402's o120 `Interface.lean`, which
copies the frozen lambdas of o105; everything else is x0405's own work on o120.)
-/
