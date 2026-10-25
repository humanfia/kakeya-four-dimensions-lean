/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

import Submission.Lib.K4ScalarCoreTools.HeavyGroups.HeavyCells
import Submission.Lib.K4ScalarCoreTools.HeavyGroups.GroupCounts
import Submission.Lib.K4ScalarCoreTools.HeavyGroups.LightGroups
import Submission.Lib.K4ScalarCoreTools.HeavyGroups.PairRestriction

import Submission.Lib.K4ScalarCoreTools.HeavyGroups.StateMixtureCaps

import Submission.Lib.K4ScalarCoreTools.HeavyGroups.FractionCleanup

import Submission.Lib.K4ScalarCoreTools.HeavyGroups.ScalarPhysicalCellCount

/-!
Adapted from: here:o062
Purpose: Original scalar group cell counts, bounded intercept overlap and stable pair breadth.

The original incidence and state measures stay unnormalized through
the Kakeya cell bound, finite overlap count and fractional mass pruning.
-/
