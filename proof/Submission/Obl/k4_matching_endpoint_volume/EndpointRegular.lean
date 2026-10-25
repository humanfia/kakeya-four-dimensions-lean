import Submission.Obl.k4_matching_endpoint_volume.EndpointBounds
import Submission.Obl.k4_matching_endpoint_volume.MatrixEstimates

/-!
# Uniform inverse bounds on regular endpoint fibers
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open Set
open scoped BigOperators Matrix

lemma endpointDerivative_lower_norm {m : ℕ} (hm : 1 ≤ m)
    (w t : Fin m → ℝ) (s : ℝ) {B d₀ : ℝ} (hB : 1 ≤ B)
    (hentry : ∀ k p : Fin m, |endpointJacobian w t s k p| ≤ B)
    (hdet : d₀ ≤ |(endpointJacobian w t s).det|) (v : Fin m → ℝ) :
    (d₀ / ((m : ℝ) * (m.factorial : ℝ) * B ^ m)) * ‖v‖ ≤
      ‖endpointDerivative w t s v‖ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hQ : 0 < (m : ℝ) * (m.factorial : ℝ) * B ^ m := by positivity
  have hmatrix := det_mul_norm_le_mulVec_norm (endpointJacobian w t s) hB hentry v
  have heval : (endpointJacobian w t s) *ᵥ v = endpointDerivative w t s v := by
    ext k
    simp only [Matrix.mulVec, dotProduct, endpointDerivative_apply]
  rw [heval] at hmatrix
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hQ).mpr
  exact (mul_le_mul_of_nonneg_right hdet (norm_nonneg v)).trans
    (by simpa only [mul_comm] using hmatrix)

/-- The internal-time regular locus used in the endpoint estimate. -/
def separatedUnitCube (m : ℕ) (q : ℝ) : Set (Fin m → ℝ) :=
  {t | ‖t‖ ≤ 1 ∧ ∀ i j : Fin m, i ≠ j → q ≤ |t j - t i|}

lemma isClosed_separatedUnitCube (m : ℕ) (q : ℝ) : IsClosed (separatedUnitCube m q) := by
  have heq : separatedUnitCube m q = Metric.closedBall 0 1 ∩
      ⋂ i : Fin m, ⋂ j : Fin m, ⋂ _h : i ≠ j, {t : Fin m → ℝ | q ≤ |t j - t i|} := by
    ext t
    simp [separatedUnitCube, Metric.mem_closedBall, dist_zero_right]
  rw [heq]
  apply Metric.isClosed_closedBall.inter
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro hij
  apply isClosed_le continuous_const
  fun_prop

lemma separatedUnitCube_subset_ball (m : ℕ) (q : ℝ) :
    separatedUnitCube m q ⊆ Metric.closedBall 0 1 := by
  intro t ht
  simpa only [Metric.mem_closedBall, dist_zero_right] using ht.1

lemma abs_offset_le_two {m : ℕ} {s : ℝ} (hs : |s| ≤ 1)
    {t : Fin m → ℝ} (ht : ‖t‖ ≤ 1) (p : Fin m) : |s - t p| ≤ 2 := by
  have hp : |t p| ≤ 1 := (norm_le_pi_norm t p).trans ht
  exact (abs_sub s (t p)).trans (by linarith)

lemma factorialProduct_pos (m : ℕ) : 0 < ∏ k : Fin m, ((k : ℕ).factorial : ℝ) := by
  apply Finset.prod_pos
  intro k hk
  exact_mod_cast Nat.factorial_pos (k : ℕ)

end Submission.Obl.k4_matching_endpoint_volume
