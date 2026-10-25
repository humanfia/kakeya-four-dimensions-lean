import Submission.Lib.K4VelocityStrips.StripFamily
import Submission.Lib.K4VelocityStrips.StripFrames
import Submission.Lib.K4VelocityStrips.StripBins

/-!
Adapted from: here:o116

Heavy velocity strip packing and whole-block frame narrowing.

Under one unchanged probability palette, separated heavy strips form a short
list, and every finite family has a separated covering net. Pairwise strip
intersections are bounded by angular ball caps. A velocity strip and one
midpoint-position bin produce a narrower frame with explicit determinant gain
and polynomial frame budgets. All width exponents and actual losses stay
explicit. This does not assert the full isotropic discovery theorem.

Original proofs developed by session x0644, building on the accepted
K4XInterface and K4FinitePlankAtlases libraries by import.
-/
