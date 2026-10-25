-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/LiftFrame.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/LiftFrame.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Mathlib

/-!
# The lifted velocity frame of a spanning velocity triple

For three planar velocities `J 0, J 1, J 2`, the matrix `A` with columns
`(1, J i)` maps the grid coordinates `u` of the Cartesian interpolation to
normalized base coordinates `z = A u`. Its first row is `(1, 1, 1)`, so the
normalized time `z 0` is the sum of the grid coordinates, and a trajectory of
velocity `J i` moves along the `i`-th grid axis at unit normalized speed.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open Matrix

noncomputable section

/-- The lifted base velocity `(1, v)`. -/
def lift (v : Fin 2 → ℝ) : Fin 3 → ℝ := ![1, v 0, v 1]

/-- The matrix whose columns are the lifted velocities `(1, J i)`. -/
def liftMatrix (J : Fin 3 → Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun r c => lift (J c) r

@[simp] theorem lift_zero (v : Fin 2 → ℝ) : lift v 0 = 1 := rfl

theorem liftMatrix_apply (J : Fin 3 → Fin 2 → ℝ) (r c : Fin 3) :
    liftMatrix J r c = lift (J c) r := rfl

/-- The normalized time of `A u` is the sum of the grid coordinates. -/
theorem liftMatrix_mulVec_zero (J : Fin 3 → Fin 2 → ℝ) (u : Fin 3 → ℝ) :
    (liftMatrix J *ᵥ u) 0 = ∑ i, u i := by
  simp [mulVec, dotProduct, liftMatrix_apply]

theorem liftMatrix_mulVec_single (J : Fin 3 → Fin 2 → ℝ) (i : Fin 3) :
    liftMatrix J *ᵥ Pi.single i 1 = lift (J i) := by
  ext r
  simp [mulVec_single, liftMatrix_apply]

/-- A right inverse of the frame sends each lifted velocity to its axis. -/
theorem inv_mulVec_lift {J : Fin 3 → Fin 2 → ℝ} {Ainv : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : liftMatrix J * Ainv = 1) (i : Fin 3) :
    Ainv *ᵥ lift (J i) = Pi.single i 1 := by
  have hA' : Ainv * liftMatrix J = 1 := mul_eq_one_comm.mp hA
  rw [← liftMatrix_mulVec_single, mulVec_mulVec, hA', one_mulVec]

theorem frame_mulVec_inv {J : Fin 3 → Fin 2 → ℝ} {Ainv : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : liftMatrix J * Ainv = 1) (x : Fin 3 → ℝ) :
    liftMatrix J *ᵥ (Ainv *ᵥ x) = x := by
  rw [mulVec_mulVec, hA, one_mulVec]

/-- Entrywise bounds give a sup-norm bound for a `3 × 3` matrix action. -/
theorem abs_mulVec_le (A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) {a b : ℝ}
    (hA : ∀ i j, |A i j| ≤ a) (hx : ∀ j, |x j| ≤ b) (i : Fin 3) :
    |(A *ᵥ x) i| ≤ 3 * a * b := by
  have hb : 0 ≤ b := (abs_nonneg _).trans (hx 0)
  have ha : 0 ≤ a := (abs_nonneg _).trans (hA 0 0)
  simp only [mulVec, dotProduct]
  calc |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, a * b := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hA i j) (hx j) (abs_nonneg _) ha
    _ = 3 * a * b := by simp; ring

theorem abs_liftMatrix_le {J : Fin 3 → Fin 2 → ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hJ : ∀ i k, |J i k| ≤ K) (r c : Fin 3) : |liftMatrix J r c| ≤ K := by
  rw [liftMatrix_apply]
  fin_cases r
  · simpa [lift] using hK
  · simpa [lift] using hJ c 0
  · simpa [lift] using hJ c 1

/-- Lifted velocities are as close as the planar velocities. -/
theorem abs_lift_sub_le {v w : Fin 2 → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ k, |v k - w k| ≤ η) (r : Fin 3) : |lift v r - lift w r| ≤ η := by
  fin_cases r
  · simpa [lift] using hη
  · simpa [lift] using h 0
  · simpa [lift] using h 1

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
