-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/FrameSubst.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/FrameSubst.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.LiftFrame
import Submission.Lib.K4ChartLifting

/-!
# Pulling a grid-coordinate polynomial back to base coordinates

A polynomial row in the grid coordinates `u = Ainv z` becomes a polynomial row
in the normalized base coordinates `z` by the linear substitution
`u_i = ∑_k Ainv i k z_k`; degrees do not increase and coefficient `ℓ¹` norms
grow at most by `(3 K)^degree`.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MvPolynomial Matrix
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg coeffL1_sum_le coeffL1_C_mul_le
  coeffL1_X eval_bind₁' totalDegree_bind₁_le_of_le_one)

noncomputable section

/-- The linear form `u_i = ∑_k Ainv i k z_k`. -/
def frameSubst (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  ∑ k, C (Ainv i k) * X k

theorem eval_frameSubst (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) (i : Fin 3) :
    eval z (frameSubst Ainv i) = (Ainv *ᵥ z) i := by
  simp [frameSubst, mulVec, dotProduct]

theorem totalDegree_frameSubst_le (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    (frameSubst Ainv i).totalDegree ≤ 1 := by
  unfold frameSubst
  apply totalDegree_finsetSum_le
  intro k _
  exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])

theorem coeffL1_frameSubst_le {Ainv : Matrix (Fin 3) (Fin 3) ℝ} {K : ℝ}
    (hA : ∀ i k, |Ainv i k| ≤ K) (i : Fin 3) : coeffL1 (frameSubst Ainv i) ≤ 3 * K := by
  unfold frameSubst
  refine (coeffL1_sum_le _ _).trans ?_
  calc ∑ k, coeffL1 (C (Ainv i k) * X k : MvPolynomial (Fin 3) ℝ)
      ≤ ∑ _k : Fin 3, K := by
        apply Finset.sum_le_sum
        intro k _
        refine (coeffL1_C_mul_le _ _).trans ?_
        rw [coeffL1_X, mul_one]
        exact hA i k
    _ = 3 * K := by simp

/-- The pulled-back row: `eval z (pullback Q) = eval (Ainv z) Q`. -/
def framePullback (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (Q : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  bind₁ (frameSubst Ainv) Q

theorem eval_framePullback (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (Q : MvPolynomial (Fin 3) ℝ)
    (z : Fin 3 → ℝ) : eval z (framePullback Ainv Q) = eval (Ainv *ᵥ z) Q := by
  unfold framePullback
  rw [eval_bind₁']
  have : (fun i => eval z (frameSubst Ainv i)) = Ainv *ᵥ z := by
    funext i
    exact eval_frameSubst Ainv z i
  rw [this]

theorem totalDegree_framePullback_le (Ainv : Matrix (Fin 3) (Fin 3) ℝ)
    (Q : MvPolynomial (Fin 3) ℝ) : (framePullback Ainv Q).totalDegree ≤ Q.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (totalDegree_frameSubst_le Ainv) Q

theorem coeffL1_framePullback_le {Ainv : Matrix (Fin 3) (Fin 3) ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hA : ∀ i k, |Ainv i k| ≤ K) (Q : MvPolynomial (Fin 3) ℝ) {D : ℕ}
    (hQ : Q.totalDegree ≤ D) :
    coeffL1 (framePullback Ainv Q) ≤ coeffL1 Q * (3 * K) ^ D := by
  have h3K : 1 ≤ 3 * K := by linarith
  refine (Submission.Lib.K4ChartLifting.coeffL1_bind₁_le _ (3 * K) h3K
    (coeffL1_frameSubst_le hA) Q).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h3K hQ) (coeffL1_nonneg Q)

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
