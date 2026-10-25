/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

import Submission.Lib.K4ScalarCoreTools.Simulation.BaseSublevel
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchSimulation
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchEndpointRecovery
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchSupport
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchMassCurl
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchGlobalMass
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchCoefficientCurl

import Submission.Lib.K4ScalarCoreTools.Simulation.ConservativePotential
import Submission.Lib.K4ScalarCoreTools.Simulation.OriginalMassQuadratic

import Submission.Lib.K4ScalarCoreTools.Simulation.RelativeMassCurl

/-!
Adapted from: here:o062
Purpose: Quantitative scalar conservativity from original joint path laws, with robust simulation, coefficient sublevels and quadratic degree restoration.

The scalar proofs are x0511's own helper proofs. The general coefficient-mass
module records its accepted here:o183/here:o151 source; the symmetric-square
volume transfer records its use of x0212's same-tree affine argument.
The prerequisite K4ScalarSwitching supplies the actual endpoint-polynomial
and regular-volume machinery without copying its implementations.
-/
