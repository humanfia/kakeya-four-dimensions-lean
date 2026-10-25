/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBoundedGrid.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBoundedGrid.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridIndices

/-! Scalar grid counts alongside the planar covering APIs. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem bounded_original_grid {Λ : Type*} (A : Set Λ) (v : Λ → ℝ) {B p : ℝ}
    (hB : 0 ≤ B) (hp : 0 < p) (hv : ∀ l ∈ A, |v l| ≤ B) :
    ∃ J : Finset ℤ, (J.card : ℝ) ≤ 2 * B / p + 3 ∧
      (∀ l ∈ A, ⌊v l / p⌋ ∈ J) ∧ ∀ j ∈ J, ∃ l ∈ A, ⌊v l / p⌋ = j :=
  bounded_scalar_grid_indices A v hB hp hv

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
