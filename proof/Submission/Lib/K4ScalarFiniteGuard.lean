/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Submission.Lib.K4ScalarFiniteGuard.Guard

/-!
# Original scalar finite-sample guards

`uniform_finiteSampleGuard` excludes buffered horizon gains for all
fixed-complexity original chart outputs, uniformly over their actual
thickness and observation exponents. The model carries the literal
scalar atlas fields; `Sampling` contains only N>=2 and N->infinity.
The genuine known-atlas exclusion is an explicit hypothesis.
-/
