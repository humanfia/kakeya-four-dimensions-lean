import Submission.Obl.k4_seven_direction_local_degree_restoration.Quadratic

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

open MvPolynomial

noncomputable def affinePoly (c : ℝ) (l : Fin 4 → ℝ) : Poly :=
  C c + ∑ i : Fin 4, C (l i) * X i

lemma affinePoly_totalDegree (c : ℝ) (l : Fin 4 → ℝ) :
    (affinePoly c l).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i hi => ?_)
  exact (totalDegree_mul _ _).trans (by simp)

lemma affinePoly_pderiv (c : ℝ) (l : Fin 4 → ℝ) (i : Fin 4) :
    pderiv i (affinePoly c l) = C (l i) := by
  simp [affinePoly, pderiv_X, Pi.single_apply]

lemma affinePoly_eval (c : ℝ) (l : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    eval x (affinePoly c l) = c + ∑ i : Fin 4, l i * x i := by
  simp [affinePoly]

lemma affinePoly_coeff_le {c Z : ℝ} {l : Fin 4 → ℝ} (hZ : 0 ≤ Z)
    (hc : |c| ≤ Z) (hl : ∀ i, |l i| ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(affinePoly c l).coeff e| ≤ 5 * Z := by
  have hsum : |(∑ i : Fin 4, C (l i) * X (R := ℝ) i).coeff e| ≤ 4 * Z := by
    rw [coeff_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin 4, |(C (l i) * X (R := ℝ) i).coeff e| ≤ ∑ _ : Fin 4, Z :=
           Finset.sum_le_sum fun i hi => abs_coeff_mul_X_le hZ (abs_coeff_C_le (hl i)) _ _
         _ = 4 * Z := by simp
  have hconst := abs_coeff_C_le hc e
  unfold affinePoly
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans (by linarith)

/-- Multiplication by an affine polynomial has only five possible contributions to each coefficient. -/
lemma affinePoly_mul_coeff_le {c Z B : ℝ} {l : Fin 4 → ℝ} {P : Poly}
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hc : |c| ≤ Z) (hl : ∀ i, |l i| ≤ Z)
    (hP : ∀ e, |P.coeff e| ≤ B) (e : Fin 4 →₀ ℕ) :
    |(affinePoly c l * P).coeff e| ≤ 5 * Z * B := by
  have hterm (i : Fin 4) : |(C (l i) * X i * P).coeff e| ≤ Z * B := by
    rw [mul_assoc, mul_comm (X i) P, coeff_C_mul, abs_mul]
    exact mul_le_mul (hl i) (abs_coeff_mul_X_le hB hP i e) (abs_nonneg _) hZ
  have hsum : |(∑ i : Fin 4, C (l i) * X i * P).coeff e| ≤ 4 * (Z * B) := by
    rw [coeff_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin 4, |(C (l i) * X i * P).coeff e| ≤ ∑ _ : Fin 4, Z * B :=
           Finset.sum_le_sum fun i hi => hterm i
         _ = 4 * (Z * B) := by simp
  have hconst : |(C c * P).coeff e| ≤ Z * B := by
    rw [coeff_C_mul, abs_mul]
    exact mul_le_mul hc (hP e) (abs_nonneg _) hZ
  unfold affinePoly
  rw [add_mul, Finset.sum_mul]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans (by linarith)

end Submission.Obl.k4_seven_direction_local_degree_restoration
