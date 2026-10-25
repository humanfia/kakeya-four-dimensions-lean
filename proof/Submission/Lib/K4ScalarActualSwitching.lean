import Submission.Lib.K4ScalarActualSwitching.PaletteRefresh
import Submission.Lib.K4ScalarActualSwitching.RestrictedRefresh
import Submission.Lib.K4ScalarActualSwitching.CompleteSwitch
import Submission.Lib.K4ScalarActualSwitching.ProjectedPaths
import Submission.Lib.K4ScalarActualSwitching.RetainedProjection
import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning
import Submission.Lib.K4ScalarActualSwitching.ActualPaths
import Submission.Lib.K4ScalarActualSwitching.ActualFourStep
import Submission.Lib.K4ScalarActualSwitching.PathCoordinates
import Submission.Lib.K4ScalarActualSwitching.ActualCoordinates
import Submission.Lib.K4ScalarActualSwitching.ActualPathSupport
import Submission.Lib.K4ScalarActualSwitching.ActualGeometry
import Submission.Lib.K4ScalarActualSwitching.BoundedIncidence
import Submission.Lib.K4ScalarActualSwitching.FiniteReference
import Submission.Lib.K4ScalarActualSwitching.StarSelection
import Submission.Lib.K4ScalarActualSwitching.StarSupport
import Submission.Lib.K4ScalarActualSwitching.OriginalBaseArea
import Submission.Lib.K4ScalarActualSwitching.StarRecovery
import Submission.Lib.K4ScalarActualSwitching.GridPalette
import Submission.Lib.K4ScalarActualSwitching.LongRowFits
import Submission.Lib.K4ScalarActualSwitching.LongRowPotential
import Submission.Lib.K4ScalarActualSwitching.NormalizedIncrements
import Submission.Lib.K4ScalarActualSwitching.DenseProductGrid
import Submission.Lib.K4ScalarActualSwitching.TensorInterpolation
import Submission.Lib.K4ScalarActualSwitching.GridSampling

/-!
Adapted from: here:o062
Purpose: Actual original incidence switches, history-aware path ceilings, signed
geometry, same-state stars, long-row fits, and finite Cartesian field preparation.

All successful measures and their original mass floors remain unnormalized.
The fixed finite reference adapter exposes its mass factors explicitly.
-/
