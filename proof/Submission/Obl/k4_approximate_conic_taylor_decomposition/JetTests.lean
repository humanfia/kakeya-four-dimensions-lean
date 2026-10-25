import Submission.Obl.k4_approximate_conic_taylor_decomposition.Forms
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Symm

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open MvPolynomial

/-- Smoothness on the radius-three ball makes every relevant Taylor tensor symmetric. -/
lemma isSymmML_iteratedFDeriv {R : E3 → ℝ}
    (hR : ContDiffOn ℝ 6 R (Metric.ball (0 : E3) 3))
    {n : ℕ} (hn : n ≤ 6) {u : E3} (hu : u ∈ Metric.closedBall (0 : E3) 2) :
    IsSymmML (iteratedFDeriv ℝ n R u) := by
  intro σ m
  exact iteratedFDeriv_comp_perm Metric.isOpen_ball hR n (by exact_mod_cast hn) u
    (Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hu) σ m

/-- The differentiated third-directional tests are the partial tests of the cubic,
quartic and quintic homogeneous Taylor forms. -/
theorem directional_form_tests {R : E3 → ℝ} (p : Fin 7 → E3) {B : ℝ}
    (hR : ContDiffOn ℝ 6 R (Metric.ball (0 : E3) 3))
    {u : E3} (hu : u ∈ Metric.closedBall (0 : E3) 2)
    (htest : ∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ ≤ B) :
    (∀ i : Fin 7, |eval (fun j => p i j) (formPoly (iteratedFDeriv ℝ 3 R u))| ≤ B) ∧
    (∀ (i : Fin 7) (j : Fin 3),
      |eval (fun j => p i j) (pderiv j (formPoly (iteratedFDeriv ℝ 4 R u)))| ≤ 4 * B) ∧
    (∀ (i : Fin 7) (j k : Fin 3),
      |eval (fun j => p i j) (pderiv j (pderiv k (formPoly (iteratedFDeriv ℝ 5 R u))))| ≤ 20 * B) := by
  have hu3 : u ∈ Metric.ball (0 : E3) 3 :=
    Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hu
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [eval_formPoly, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      htest i 0 (by norm_num)
  · intro i j
    have hsymm := isSymmML_iteratedFDeriv hR (by norm_num : 4 ≤ 6) hu
    rw [eval_pderiv_formPoly _ hsymm]
    have hval := fderiv_iteratedFDeriv_apply_const Metric.isOpen_ball hR
      (by norm_num : ((3 + 1 : ℕ) : WithTop ℕ∞) ≤ 6) hu3 (fun _ => p i) (e3 j)
    have hb : |iteratedFDeriv ℝ 4 R u (Fin.cons (e3 j) (fun _ => p i))| ≤ B := by
      rw [← hval]
      calc
        |fderiv ℝ (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u (e3 j)|
            ≤ ‖fderiv ℝ (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ * ‖e3 j‖ :=
          by simpa only [Real.norm_eq_abs] using ((fderiv ℝ (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u).le_opNorm (e3 j))
        _ ≤ B := by simpa only [norm_e3, mul_one, ← norm_iteratedFDeriv_one] using htest i 1 (by norm_num)
    norm_num only [Nat.cast_ofNat, add_zero, zero_add, abs_mul]
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  · intro i j k
    have hsymm := isSymmML_iteratedFDeriv hR (by norm_num : 5 ≤ 6) hu
    rw [eval_pderiv_pderiv_formPoly _ hsymm]
    have hval := iteratedFDeriv_two_iteratedFDeriv_apply_const Metric.isOpen_ball hR
      (by norm_num : ((3 + 2 : ℕ) : WithTop ℕ∞) ≤ 6) hu3 (fun _ => p i) (e3 k) (e3 j)
    have hb : |iteratedFDeriv ℝ 5 R u (Fin.cons (e3 k) (Fin.cons (e3 j) (fun _ => p i)))| ≤ B := by
      rw [← hval]
      calc
        |iteratedFDeriv ℝ 2 (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u ![e3 k, e3 j]|
            ≤ ‖iteratedFDeriv ℝ 2 (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ *
              ∏ l : Fin 2, ‖(![e3 k, e3 j] : Fin 2 → E3) l‖ :=
          by simpa only [Real.norm_eq_abs] using ((iteratedFDeriv ℝ 2 (fun v : E3 => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u).le_opNorm ![e3 k, e3 j])
        _ ≤ B := by simpa [Fin.prod_univ_two, norm_e3] using htest i 2 (by norm_num)
    norm_num only [Nat.cast_ofNat, add_zero, zero_add, abs_mul]
    nlinarith only [hb]

/-- The unnormalized Taylor forms have a common coefficient bound. -/
lemma coeff_formPoly_iteratedFDeriv_le {R : E3 → ℝ} {A : ℝ} (hA : 2 ≤ A)
    (hbound : ∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : E3) 2,
      ‖iteratedFDeriv ℝ j R u‖ ≤ A)
    {n : ℕ} (hn : n ≤ 5) {u : E3} (hu : u ∈ Metric.closedBall (0 : E3) 2)
    (m : Fin 3 →₀ ℕ) : |(formPoly (iteratedFDeriv ℝ n R u)).coeff m| ≤ A ^ 9 := by
  have hA0 : 0 ≤ A := by linarith
  calc
    _ ≤ 3 ^ n * ‖iteratedFDeriv ℝ n R u‖ := coeff_formPoly_abs_le _ _
    _ ≤ 3 ^ 5 * A := mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hn)
      (hbound n (by omega) u hu) (norm_nonneg _) (by norm_num)
    _ ≤ A ^ 8 * A := mul_le_mul_of_nonneg_right (by
      calc (3 : ℝ) ^ 5 ≤ 2 ^ 8 := by norm_num
           _ ≤ A ^ 8 := pow_le_pow_left₀ (by norm_num) hA 8) hA0
    _ = A ^ 9 := by ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition
