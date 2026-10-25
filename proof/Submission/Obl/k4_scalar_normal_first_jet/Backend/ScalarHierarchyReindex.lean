/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyReindex.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyReindex.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridHierarchy

/-! Every finite bridge reads the same stored original hierarchy and final row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

namespace ScalarGridHierarchy

def reindex {Λ : Type*} [MeasurableSpace Λ] {n m : ℕ}
    {ν : MeasureTheory.Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin n → ℝ} {B : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (r : Fin m → Fin n) :
    ScalarGridHierarchy ν E F (fun i => J (r i)) (fun i => hJ (r i)) (fun i => p (r i)) B where
  times := G.times
  slope := fun i => G.slope (r i)
  intercept := fun i => G.intercept (r i)
  measurable_times := G.measurable_times
  unit_time := G.unit_time
  active_time := G.active_time
  measurable_slope := fun i => G.measurable_slope (r i)
  measurable_intercept := fun i => G.measurable_intercept (r i)
  bounded := fun i => G.bounded (r i)
  mass := G.mass
  time_floor := G.time_floor
  constant_on_grid := fun i => G.constant_on_grid (r i)
  fit := fun i => G.fit (r i)

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
