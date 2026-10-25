import Submission.Lib.K4FinitePlankAtlases.FiniteDensity
import Submission.Lib.K4FinitePlankAtlases.TimeBounds
import Submission.Lib.K4FinitePlankAtlases.ContinuousAtlas
import Submission.Lib.K4FinitePlankAtlases.DensityFloors
import Submission.Lib.K4FinitePlankAtlases.BlockMarginals
import Submission.Lib.K4FinitePlankAtlases.FormatBounds
import Submission.Lib.K4FinitePlankAtlases.AssignmentLift

/-!
# Disjoint finite true atlases for finite and continuous trace laws

Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank theorem is an explicit input. The atlas retains at least half
of the given marked mass, with original unnormalized per-packet Jacobian floors,
bounded centers, and quantitative frame and inverse-frame bounds. Selected-time
quadratic estimates also extend to entire blocks with a fixed power loss.

For a continuous original law, mesh-scale caps suffice: assignments are the
first fitting whole-trace planks, independent of the internal mark table or
coefficient approximation. The output retains half of the given original mass.
Density-floor transfer and original whole-cell witnesses supply the cell-count
budget; block marginals identify the output floors with original incidence mass.
A fixed polynomial chart-count exponent is uniform over all loss exponents in [0,1].
-/
