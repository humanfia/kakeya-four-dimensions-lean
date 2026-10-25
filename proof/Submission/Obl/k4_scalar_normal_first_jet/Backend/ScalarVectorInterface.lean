/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarVectorInterface.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarVectorInterface.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarMotion
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Normalized coefficient vectors and the primitive scalar-motion interface. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

namespace ScalarMotion

/-- In normalized coordinates, the quadratic coefficients precede
the two affine coefficients. -/
def ofCoefficientVector {Λ : Type*} [MeasurableSpace Λ]
    (c : Λ → Fin 5 → ℝ) (hc : Measurable c) : ScalarMotion Λ where
  x₀ := fun l => c l 0
  x₁ := fun l => c l 1
  x₂ := fun l => c l 2
  y₀ := fun l => c l 3
  y₁ := fun l => c l 4
  measurable_x₀ := (measurable_pi_apply 0).comp hc
  measurable_x₁ := (measurable_pi_apply 1).comp hc
  measurable_x₂ := (measurable_pi_apply 2).comp hc
  measurable_y₀ := (measurable_pi_apply 3).comp hc
  measurable_y₁ := (measurable_pi_apply 4).comp hc

theorem ofCoefficientVector_bounded {Λ : Type*} [MeasurableSpace Λ]
    (c : Λ → Fin 5 → ℝ) (hc : Measurable c) {K : ℝ} {l : Λ}
    (h : ∀ i, |c l i| ≤ K) : (ofCoefficientVector c hc).Bounded K l :=
  ⟨h 0, h 1, h 2, h 3, h 4⟩

end ScalarMotion

theorem scalar_norm_three_le_sum_abs (v : Fin 3 → ℝ) :
    ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |v 0| ≤ |v 0| + |v 1| + |v 2|
    linarith [abs_nonneg (v 1), abs_nonneg (v 2)]
  · change |v 1| ≤ |v 0| + |v 1| + |v 2|
    linarith [abs_nonneg (v 0), abs_nonneg (v 2)]
  · change |v 2| ≤ |v 0| + |v 1| + |v 2|
    linarith [abs_nonneg (v 0), abs_nonneg (v 1)]

/-- The original supremum-norm residual comparison implies the
sum-of-coordinate comparison used by the stored scalar-normal data. -/
theorem ScalarMotion.residual_comparison_of_norm {Λ : Type*} [MeasurableSpace Λ]
    (D : ScalarMotion Λ) {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {K ζ : ℝ} (hK : 0 ≤ K)
    (hres : ∀ p ∈ E, ∀ q ∈ E,
      |D.residual F p.1 p.2 - D.residual F q.1 q.2| ≤
        K * (‖(![p.2, D.x p.1 p.2, D.y p.1 p.2] : Fin 3 → ℝ) -
          ![q.2, D.x q.1 q.2, D.y q.1 q.2]‖ + ζ)) :
    ∀ p ∈ E, ∀ q ∈ E,
      |D.residual F p.1 p.2 - D.residual F q.1 q.2| ≤
        K * (|p.2 - q.2| + |D.x p.1 p.2 - D.x q.1 q.2| +
          |D.y p.1 p.2 - D.y q.1 q.2| + ζ) := by
  intro p hp q hq
  have hnorm : ‖(![p.2, D.x p.1 p.2, D.y p.1 p.2] : Fin 3 → ℝ) -
      ![q.2, D.x q.1 q.2, D.y q.1 q.2]‖ ≤
      |p.2 - q.2| + |D.x p.1 p.2 - D.x q.1 q.2| + |D.y p.1 p.2 - D.y q.1 q.2| := by
    simpa using
      scalar_norm_three_le_sum_abs
        ((![p.2, D.x p.1 p.2, D.y p.1 p.2] : Fin 3 → ℝ) -
          ![q.2, D.x q.1 q.2, D.y q.1 q.2])
  exact (hres p hp q hq).trans
    (mul_le_mul_of_nonneg_left (add_le_add hnorm le_rfl) hK)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
