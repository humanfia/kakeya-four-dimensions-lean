/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLocalFitConstants.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLocalFitConstants.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionMeasureModel

/-! Explicit original mass and active-time length in the local fit. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable def scalarNormalizedCollisionMass (p K d δ : ℝ) : ℝ :=
  (δ ^ 2 / (3 * (K * ((2 * K) / p) ^ d))) / (3 * (K * ((2 * K) / p) ^ d))

noncomputable def scalarNormalizedActiveLength (p K d error δ : ℝ) : ℝ :=
  scalarNormalizedCollisionMass p K d δ /
    (4 * ((2 * K / p + 3) ^ 2 * scalarCollisionPairCeiling p K d K (1 + 2 * error)) * (2 / p + 4))

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
