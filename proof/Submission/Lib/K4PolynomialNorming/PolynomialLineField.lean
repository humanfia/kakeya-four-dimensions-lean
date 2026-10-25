/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

open MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

/-- Restriction to an affine trajectory, in arbitrary base coordinates. -/
noncomputable def affineTrajectoryPolynomial {σ : Type*} (c u : σ → ℝ) :
    MvPolynomial σ ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (u i)*Polynomial.X+Polynomial.C (c i))

theorem affineTrajectoryPolynomial_eval {σ : Type*}
    (c u : σ → ℝ) (F : MvPolynomial σ ℝ) (t : ℝ) :
    (affineTrajectoryPolynomial c u F).eval t = MvPolynomial.eval (c+t • u) F := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp [affineTrajectoryPolynomial]
  | add P Q hP hQ =>
    simpa only [map_add,Polynomial.eval_add] using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    simp only [map_mul,MvPolynomial.aeval_X,Polynomial.eval_mul,MvPolynomial.eval_X,
      affineTrajectoryPolynomial] at hP ⊢
    rw [hP]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring

theorem affineTrajectoryPolynomial_natDegree_le {σ : Type*}
    (c u : σ → ℝ) (F : MvPolynomial σ ℝ) :
    (affineTrajectoryPolynomial c u F).natDegree ≤ F.totalDegree := by
  have hlinear : ∀ i : σ,
      (Polynomial.C (u i)*Polynomial.X+Polynomial.C (c i)).natDegree ≤ 1 :=
    fun _ => Polynomial.natDegree_linear_le
  simpa only [affineTrajectoryPolynomial,Nat.mul_one] using MvPolynomial.aeval_natDegree_le F le_rfl
    (fun i => Polynomial.C (u i)*Polynomial.X+Polynomial.C (c i)) hlinear

/-- The actual quadratic-height derivative minus the field contraction
along its affine base is one univariate polynomial. -/
noncomputable def quadraticLineFieldResidual {σ : Type*} [Fintype σ]
    (T : σ → MvPolynomial σ ℝ) (c u : σ → ℝ) (b d : ℝ) : Polynomial ℝ :=
  Polynomial.C b+Polynomial.C (2*d)*Polynomial.X-
    ∑ j, Polynomial.C (u j)*affineTrajectoryPolynomial c u (T j)

theorem quadraticLineFieldResidual_eval {σ : Type*} [Fintype σ]
    (T : σ → MvPolynomial σ ℝ) (c u : σ → ℝ) (b d t : ℝ) :
    (quadraticLineFieldResidual T c u b d).eval t =
      b+2*t*d-∑ j, u j*MvPolynomial.eval (c+t • u) (T j) := by
  simp only [quadraticLineFieldResidual,Polynomial.eval_sub,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_finsetSum,
    affineTrajectoryPolynomial_eval]
  ring

theorem quadraticLineFieldResidual_natDegree_le {σ : Type*} [Fintype σ]
    (T : σ → MvPolynomial σ ℝ) (c u : σ → ℝ) (b d : ℝ)
    (D : ℕ) (hD : ∀ j, (T j).totalDegree ≤ D) :
    (quadraticLineFieldResidual T c u b d).natDegree ≤ D+1 := by
  unfold quadraticLineFieldResidual
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp
    · calc
        _ ≤ (Polynomial.C (2*d)).natDegree+(Polynomial.X : Polynomial ℝ).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ D+1 := by
          simp only [Polynomial.natDegree_C,Polynomial.natDegree_X,zero_add]
          exact Nat.succ_le_succ (Nat.zero_le D)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((affineTrajectoryPolynomial_natDegree_le c u (T j)).trans ((hD j).trans (Nat.le_succ D)))

end Submission.Lib.K4PolynomialNorming
