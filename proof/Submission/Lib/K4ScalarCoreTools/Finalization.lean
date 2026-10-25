import Submission.Lib.K4ScalarCoreTools.Finalization.PriorWeightedGroups
/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

import Submission.Lib.K4ScalarCoreTools.Finalization.CartesianVectorField
import Submission.Lib.K4ScalarCoreTools.Finalization.CartesianOriginalMass
import Submission.Lib.K4ScalarCoreTools.Finalization.Pruning
import Submission.Lib.K4ScalarCoreTools.Finalization.PolynomialBinLists
import Submission.Lib.K4ScalarCoreTools.Finalization.FiniteBinChoice
import Submission.Lib.K4ScalarCoreTools.Finalization.CartesianCells
import Submission.Lib.K4ScalarCoreTools.Finalization.FinitePaletteFreeze
import Submission.Lib.K4ScalarCoreTools.Finalization.Interpolation
import Submission.Lib.K4ScalarCoreTools.Finalization.ScalarResidual
import Submission.Lib.K4ScalarCoreTools.Finalization.Format
import Submission.Lib.K4ScalarCoreTools.Finalization.InterceptAssignments
import Submission.Lib.K4ScalarCoreTools.Finalization.ScalarInterceptOverlap
import Submission.Lib.K4ScalarCoreTools.Finalization.OriginalPathsPotential
import Submission.Lib.K4ScalarCoreTools.Finalization.RelativeMassQuadratic
import Submission.Lib.K4ScalarCoreTools.Finalization.ListMultiplicity
import Submission.Lib.K4ScalarCoreTools.Finalization.TimeSampling
import Submission.Lib.K4ScalarCoreTools.Finalization.PolynomialBinSampling
import Submission.Lib.K4ScalarCoreTools.Finalization.PolynomialBinPower

/-!
Adapted from: here:o062
Purpose: Original-mass quadratic recovery, geometric intercept assignments, physical group counts and original-time polynomial-bin sampling.
Original application proofs: x0511; independent uniform-time sampling: x0212.
Generic adapted prerequisites retain exact accepted-source credits in their modules.
-/
