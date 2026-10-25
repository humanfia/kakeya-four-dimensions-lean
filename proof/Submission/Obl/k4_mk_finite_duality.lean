import Mathlib
import ChallengeDeps
import Submission.Obl.k4_mk_finite_duality.Scalar
import Submission.Obl.k4_mk_finite_duality.Tuple
set_option linter.unusedVariables false

open scoped BigOperators
open Submission.Obl.k4_mk_finite_duality

/-!
# `Submission.k4_mk_finite_duality`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_mk_finite_duality`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_mk_finite_duality/`
belong to this obligation.
-/

theorem Submission.k4_mk_finite_duality : ∀ n : ℕ, 2 ≤ n → ∀ K : ℝ, 0 < K → ∀ (m : ℕ) (N : Fin n → ℕ) (e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n)) (b : Fin m → (i : Fin n) → Fin (N i) → ℝ), (∀ (q : Fin m) (i : Fin n) (k : Fin (N i)), 0 ≤ b q i k) → (∀ M : Fin m → ℝ, (∀ q : Fin m, 0 ≤ M q) → (∑ q : Fin m, M q) = 1 → ∃ A : Fin m → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)), (∀ q : Fin m, M q ≤ |LinearMap.det (A q)|) ∧ ∀ (i : Fin n) (k : Fin (N i)), (∑ q : Fin m, b q i k * ‖A q (e i k)‖) ≤ K) → ∀ w : (i : Fin n) → Fin (N i) → ℝ, (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) → (∑ q : Fin m, (∑ T : ((i : Fin n) → Fin (N i)), |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| * ∏ i : Fin n, (w i (T i) * b q i (T i))) ^ ((1 : ℝ) / ((n : ℝ) - 1))) ≤ K ^ ((n : ℝ) / ((n : ℝ) - 1)) * ∏ i : Fin n, (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  classical
  intro n hn K hK m N e b hb hfactor w hw
  let F : Fin m → ℝ := fun q =>
    ∑ T : ((i : Fin n) → Fin (N i)),
      |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| *
        ∏ i : Fin n, (w i (T i) * b q i (T i))
  have hF : ∀ q, 0 ≤ F q := fun q =>
    Finset.sum_nonneg (fun T _ => mul_nonneg (abs_nonneg _)
      (Finset.prod_nonneg (fun i _ => mul_nonneg (hw i (T i)) (hb q i (T i)))))
  let W : Fin n → ℝ := fun i => ∑ k, w i k
  have hW : ∀ i, 0 ≤ W i := fun i => Finset.sum_nonneg (fun k _ => hw i k)
  have hdual : (∑ q, F q ^ (1 / ((n : ℝ) - 1))) ≤
      (∏ i, K * W i) ^ (1 / ((n : ℝ) - 1)) := by
    apply finite_duality_scalar hn F hF (fun i => K * W i)
      (fun i => mul_nonneg hK.le (hW i))
    intro M hM hMsum
    obtain ⟨A, hdet, hbudget⟩ := hfactor M hM hMsum
    refine ⟨(fun i q => ∑ k, w i k * b q i k * ‖A q (e i k)‖), ?_, ?_, ?_⟩
    · intro i q
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (mul_nonneg (hw i k) (hb q i k)) (norm_nonneg _))
    · intro q
      exact mul_tuple_sum_le e (A q) (fun i k => w i k * b q i k)
        (fun i k => mul_nonneg (hw i k) (hb q i k)) (hdet q)
    · intro i
      calc
        (∑ q, ∑ k, w i k * b q i k * ‖A q (e i k)‖) =
            ∑ k, w i k * ∑ q, b q i k * ‖A q (e i k)‖ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          ring
        _ ≤ ∑ k, w i k * K := Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hbudget i k) (hw i k))
        _ = K * W i := by rw [← Finset.sum_mul]; exact mul_comm _ _
  rw [budget_product K hK.le W hW] at hdual
  exact hdual
