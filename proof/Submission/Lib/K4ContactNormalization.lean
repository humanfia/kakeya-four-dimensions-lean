import Submission.Lib.K4ContactNormalization.RowNormalization
import Submission.Lib.K4ContactNormalization.ResidualNormalization
import Submission.Lib.K4ContactNormalization.HomogeneousCorrection
import Submission.Lib.K4ContactNormalization.AffineTimeTransfer

/-!
# Affine contact normalization and homogeneous hidden-test calibration

Adapted from: here:o200 (session x0696).

Exact row/skew algebra, affine residual trajectory normalization, full-block
fit transport, original-mass coefficient calibration, and affine extrapolation
from arbitrary long-time witness sets. The homogeneous calibration uses a base
correction of the original test and requires no bound on the affine predictor.
-/
