import Mathlib
import ChallengeDeps
import Submission.Obl.k4_seven_direction_third_derivative_bound.CubicPowerBound
import Submission.Obl.k4_seven_direction_third_derivative_bound.ThirdBound
set_option linter.unusedVariables false

/-!
# `Submission.k4_seven_direction_third_derivative_bound`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_seven_direction_third_derivative_bound`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_seven_direction_third_derivative_bound/`
belong to this obligation.
-/

namespace Submission.Obl.k4_seven_direction_third_derivative_bound

/-- Four of the seven conditioned directions already give the cubic estimate. -/
theorem two_copy_cubic : TwoCopyCubicProp := by
  refine ⟨126, by norm_num, ?_⟩
  intro A ε hA hε p hp hdet T h01 h12 htest
  let e : Fin 4 → Fin 7 := Fin.castLE (by decide)
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin 7 => z.val) hij)
  exact cubic_two_copy_coefficients_le_power (fun i => p (e i)) A ε hA hε
    (fun i j => hp (e i) j)
    (fun i j k hij hik hjk => hdet (e i) (e j) (e k)
      (he.ne hij) (he.ne hik) (he.ne hjk))
    T h01 h12 (fun i j => htest (e i) j)

end Submission.Obl.k4_seven_direction_third_derivative_bound

theorem Submission.k4_seven_direction_third_derivative_bound : ∃ K : ℕ, 1 ≤ K ∧ ∀ (A η : ℝ) (f : (EuclideanSpace ℝ (Fin 3)) → ℝ) (p : Fin 7 → (EuclideanSpace ℝ (Fin 3))), 2 ≤ A → 0 ≤ η → ContDiffOn ℝ 6 f (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) 3) → (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) → (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) → (∀ i : Fin 7, ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖fderiv ℝ (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ ≤ A * η) → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ 3 f u‖ ≤ A ^ K * η := by
  obtain ⟨K, hK⟩ :=
    Submission.Obl.k4_seven_direction_third_derivative_bound.norm_third_le_of_two_copy
      Submission.Obl.k4_seven_direction_third_derivative_bound.two_copy_cubic
  refine ⟨K + 1, by omega, ?_⟩
  intro A η f p hA hη hf hp hdet htest u hu
  have hu3 : u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 3 :=
    Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hu).trans_lt (by norm_num))
  have hf3 : ContDiffOn ℝ 3 f (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 3) :=
    hf.of_le (by norm_num)
  have hbound := hK A (A * η) f p (Metric.ball 0 3) hA
    (mul_nonneg (by linarith) hη) Metric.isOpen_ball hf3 (fun i => (hp i).2) hdet u hu3
    (fun i => by simpa only [norm_iteratedFDeriv_one] using htest i u hu)
  calc
    ‖iteratedFDeriv ℝ 3 f u‖ ≤ A ^ K * (A * η) := hbound
    _ = A ^ (K + 1) * η := by rw [pow_succ]; ring
