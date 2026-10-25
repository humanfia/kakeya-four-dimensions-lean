/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarADCollisions.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarADCollisions.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridCollisions
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCovers

/-! Original scalar collisions from the actual interval support bound. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

/-- The scalar support bound itself supplies all occupied lists needed for
the collision lower bound. Time-dependent lists are selected after fixing
the support, and the original trajectory and time laws remain unchanged. -/
theorem original_intervalAD_collision_lower {Θ Λ : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Λ]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (ν : Measure Λ) [IsFiniteMeasure ν]
    {E : Set (Θ × Λ)} (hE : MeasurableSet E) {F : Θ × Λ → ℝ} (hF : Measurable F)
    {p d C R a : ℝ} (hp : 0 < p) (hpR : p ≤ R) (S : Θ → Set ℝ)
    (hS : ∀ θ, IntervalAD p d C (S θ))
    (hsupport : ∀ θ l, (θ, l) ∈ E → F (θ, l) ∈ S θ ∩ Icc a (a + R)) :
    ((μ.prod ν).real E) ^ 2 ≤ (3 * (C * (R / p) ^ d)) * ∫ θ,
      (ν.prod ν).real {q : Λ × Λ | (θ, q.1) ∈ E ∧ (θ, q.2) ∈ E ∧
        (⌊F (θ, q.1) / p⌋ : ℤ) = ⌊F (θ, q.2) / p⌋} ∂μ := by
  classical
  choose K hcard hcover using fun θ => intervalAD_grid_list (a := a) hp hpR (hS θ)
  exact original_grid_collision_lower μ ν hE
    (Int.measurable_floor.comp (hF.div_const p)) K
    (fun θ l hl => hcover θ _ (hsupport θ l hl)) hcard

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
