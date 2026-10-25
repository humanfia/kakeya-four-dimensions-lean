/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open Set MeasureTheory MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

/-- Move the first coordinate to the end, retaining the tail in its natural order. -/
noncomputable def splitHeadCoordinates (n : ℕ) :
    (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).trans MeasurableEquiv.prodComm

theorem splitHeadCoordinates_measurePreserving (n : ℕ) : MeasurePreserving (splitHeadCoordinates n) :=
  Measure.measurePreserving_swap.comp (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)

theorem splitHeadCoordinates_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    splitHeadCoordinates n x = (Fin.tail x, x 0) := by rfl

theorem splitHeadCoordinates_symm_apply (n : ℕ) (x : Fin n → ℝ) (t : ℝ) :
    (splitHeadCoordinates n).symm (x,t) = Fin.cons t x := by
  apply (splitHeadCoordinates n).injective
  rw [MeasurableEquiv.apply_symm_apply, splitHeadCoordinates_apply]
  rfl

theorem volume_unit_coordinate_box (n : ℕ) :
    volume (Set.Icc (-1 : Fin n → ℝ) 1) = ENNReal.ofReal ((2:ℝ) ^ n) := by
  rw [Real.volume_Icc_pi]
  norm_num

/-- A common power increase pays both the outer fiber loss and the volume
of the remaining coordinate box. -/
theorem norming_enlargement_bounds (A : ℝ) (hA : 2 ≤ A) (n : ℕ) :
    2 ≤ A ^ (n + 3) ∧ 4 * A ≤ A ^ (n + 3) ∧
      (2 * (2:ℝ)^n) * A ≤ A ^ (n + 3) := by
  have hA0 : 0 ≤ A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hpow : (2:ℝ) ^ (n + 2) ≤ A ^ (n + 2) := pow_le_pow_left₀ (by norm_num) hA _
  have h4 : (4:ℝ) ≤ A ^ (n + 2) := by
    calc
      _ ≤ (2:ℝ) ^ (n + 2) := by
        have h := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := n)
        rw [pow_add]; norm_num; linarith
      _ ≤ _ := hpow
  have hcoef : 2 * (2:ℝ) ^ n ≤ A ^ (n + 2) := by
    apply le_trans _ hpow
    rw [pow_add]; norm_num; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
  have hp : A ^ (n + 3) = A ^ (n + 2) * A := by rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
  refine ⟨?_, ?_, ?_⟩
  · exact hA.trans (by
      calc
        A = 1 * A := (one_mul A).symm
        _ ≤ A ^ (n + 2) * A := mul_le_mul_of_nonneg_right (one_le_pow₀ hA1) hA0
        _ = _ := hp.symm)
  · rw [hp]; exact mul_le_mul_of_nonneg_right h4 hA0
  · rw [hp]; exact mul_le_mul_of_nonneg_right hcoef hA0

end Submission.Lib.K4PolynomialNorming
