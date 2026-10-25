import Submission.Obl.k4_matching_endpoint_volume.Endpoint

/-!
# Uniform bounds for the endpoint derivative

All constants grow polynomially in the bound for the controls. The number of
jets is fixed throughout the two-color matching argument.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open scoped BigOperators Matrix NNReal

lemma endpointJacobian_entry_bound {m : ℕ} (w t : Fin m → ℝ) (s : ℝ)
    {W B : ℝ} (hW : 0 ≤ W) (hB : 1 ≤ B)
    (hw : ∀ p : Fin m, |w p| ≤ W) (ht : ∀ p : Fin m, |s - t p| ≤ B)
    (k p : Fin m) : |endpointJacobian w t s k p| ≤ W * B ^ m := by
  have hfact : (1 : ℝ) ≤ (k : ℕ).factorial := by
    have hf : 1 ≤ (k : ℕ).factorial := Nat.factorial_pos _
    exact_mod_cast hf
  have hp : |s - t p| ^ (k : ℕ) ≤ B ^ m :=
    (pow_le_pow_left₀ (abs_nonneg _) (ht p) _).trans
      (pow_le_pow_right₀ hB (by omega : (k : ℕ) ≤ m))
  calc
    |endpointJacobian w t s k p| = |w p| * |s - t p| ^ (k : ℕ) /
        ((k : ℕ).factorial : ℝ) := by
      simp [endpointJacobian, abs_mul, abs_div, abs_pow]
    _ ≤ |w p| * |s - t p| ^ (k : ℕ) :=
      div_le_self (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) hfact
    _ ≤ W * B ^ m := mul_le_mul (hw p) hp (pow_nonneg (abs_nonneg _) _) hW

lemma endpointJacobian_entry_sub_bound {m : ℕ} (w t u : Fin m → ℝ) (s : ℝ)
    {W B : ℝ} (hW : 0 ≤ W) (hB : 1 ≤ B)
    (hw : ∀ p : Fin m, |w p| ≤ W)
    (ht : ∀ p : Fin m, |s - t p| ≤ B) (hu : ∀ p : Fin m, |s - u p| ≤ B)
    (k p : Fin m) :
    |endpointJacobian w t s k p - endpointJacobian w u s k p| ≤
      (W * (m : ℝ) * B ^ m) * ‖t - u‖ := by
  have hfact : (1 : ℝ) ≤ (k : ℕ).factorial := by
    have hf : 1 ≤ (k : ℕ).factorial := Nat.factorial_pos _
    exact_mod_cast hf
  have hpow := abs_pow_sub_pow_le (a := s - t p) (b := s - u p) (n := (k : ℕ))
  have hsub : |(s - t p) - (s - u p)| = |t p - u p| := by
    rw [show (s - t p) - (s - u p) = -(t p - u p) by ring, abs_neg]
  rw [hsub] at hpow
  have hm : ((k : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : (k : ℕ) ≤ m)
  have hp : max |s - t p| |s - u p| ^ ((k : ℕ) - 1) ≤ B ^ m :=
    (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le (ht p) (hu p)) _).trans
      (pow_le_pow_right₀ hB (by omega : (k : ℕ) - 1 ≤ m))
  have hd : |t p - u p| ≤ ‖t - u‖ := norm_le_pi_norm (t - u) p
  have hdiff : |(s - t p) ^ (k : ℕ) - (s - u p) ^ (k : ℕ)| ≤
      ‖t - u‖ * (m : ℝ) * B ^ m := by
    apply hpow.trans
    exact mul_le_mul (mul_le_mul hd hm (Nat.cast_nonneg _) (norm_nonneg _)) hp
      (pow_nonneg (le_max_of_le_left (abs_nonneg _)) _) (by positivity)
  have heq : endpointJacobian w t s k p - endpointJacobian w u s k p =
      -w p * ((s - t p) ^ (k : ℕ) - (s - u p) ^ (k : ℕ)) /
        ((k : ℕ).factorial : ℝ) := by unfold endpointJacobian; ring
  rw [heq, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ (k : ℕ).factorial from Nat.cast_nonneg _)]
  calc
    |w p| * |(s - t p) ^ (k : ℕ) - (s - u p) ^ (k : ℕ)| / ((k : ℕ).factorial : ℝ) ≤
        |w p| * |(s - t p) ^ (k : ℕ) - (s - u p) ^ (k : ℕ)| :=
      div_le_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hfact
    _ ≤ W * (‖t - u‖ * (m : ℝ) * B ^ m) :=
      mul_le_mul (hw p) hdiff (abs_nonneg _) hW
    _ = (W * (m : ℝ) * B ^ m) * ‖t - u‖ := by ring

lemma endpointDerivative_apply {m : ℕ} (w t : Fin m → ℝ) (s : ℝ)
    (v : Fin m → ℝ) (k : Fin m) :
    endpointDerivative w t s v k = ∑ p : Fin m, endpointJacobian w t s k p * v p := by
  simp only [endpointDerivative, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

lemma endpointDerivative_sub_norm_bound {m : ℕ} (w t u : Fin m → ℝ) (s : ℝ)
    {W B : ℝ} (hW : 0 ≤ W) (hB : 1 ≤ B)
    (hw : ∀ p : Fin m, |w p| ≤ W)
    (ht : ∀ p : Fin m, |s - t p| ≤ B) (hu : ∀ p : Fin m, |s - u p| ≤ B) :
    ‖endpointDerivative w t s - endpointDerivative w u s‖ ≤
      (W * (m : ℝ) ^ 2 * B ^ m) * ‖t - u‖ := by
  have hB0 : 0 ≤ B := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  have heval : ((endpointDerivative w t s - endpointDerivative w u s) v) k =
      ∑ p : Fin m, (endpointJacobian w t s k p - endpointJacobian w u s k p) * v p := by
    simp only [sub_apply, Pi.sub_apply, endpointDerivative_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [heval, Real.norm_eq_abs]
  calc
    |∑ p : Fin m, (endpointJacobian w t s k p - endpointJacobian w u s k p) * v p| ≤
        ∑ p : Fin m, |(endpointJacobian w t s k p - endpointJacobian w u s k p) * v p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin m, ((W * (m : ℝ) * B ^ m) * ‖t - u‖) * ‖v‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul (endpointJacobian_entry_sub_bound w t u s hW hB hw ht hu k p)
        (norm_le_pi_norm v p) (abs_nonneg _) (by positivity)
    _ = (W * (m : ℝ) ^ 2 * B ^ m) * ‖t - u‖ * ‖v‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma endpointDerivative_lipschitzOn_unitCube {m : ℕ} (w : Fin m → ℝ) {s W : ℝ}
    (hs : |s| ≤ 1) (hW : 0 ≤ W) (hw : ∀ p : Fin m, |w p| ≤ W) :
    LipschitzOnWith (⟨W * (m : ℝ) ^ 2 * (2 : ℝ) ^ m, by positivity⟩ : ℝ≥0)
      (fun t : Fin m → ℝ => endpointDerivative w t s) (Metric.closedBall 0 1) := by
  refine (lipschitzOnWith_iff_norm_sub_le).2 ?_
  intro t ht u hu
  apply endpointDerivative_sub_norm_bound w t u s hW (by norm_num) hw
  · intro p
    have hnorm : ‖t‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
    have hp : |t p| ≤ 1 := (norm_le_pi_norm t p).trans hnorm
    exact (abs_sub s (t p)).trans (by linarith)
  · intro p
    have hnorm : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    have hp : |u p| ≤ 1 := (norm_le_pi_norm u p).trans hnorm
    exact (abs_sub s (u p)).trans (by linarith)

/-- A deliberately loose polynomial lower bound for the Vandermonde determinant. -/
lemma endpointJacobian_det_lower {m : ℕ} (w t : Fin m → ℝ) (s : ℝ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hw : ∀ p : Fin m, q ≤ |w p|)
    (ht : ∀ p r : Fin m, p ≠ r → q ≤ |t r - t p|) :
    q ^ (m + m * m) / (∏ k : Fin m, ((k : ℕ).factorial : ℝ)) ≤
      |(endpointJacobian w t s).det| := by
  rw [abs_det_endpointJacobian]
  have hwp : q ^ m ≤ ∏ p : Fin m, |w p| := by
    calc
      q ^ m = ∏ _p : Fin m, q := by simp
      _ ≤ ∏ p : Fin m, |w p| := Finset.prod_le_prod₀ (fun p hp => hq0) (fun p hp => hw p)
  have htp (p : Fin m) : q ^ m ≤ ∏ r ∈ Finset.Ioi p, |t r - t p| := by
    calc
      q ^ m ≤ q ^ (Finset.Ioi p).card :=
        pow_le_pow_of_le_one hq0 hq1 (by simpa using Finset.card_le_univ (Finset.Ioi p))
      _ = ∏ _r ∈ Finset.Ioi p, q := by simp
      _ ≤ ∏ r ∈ Finset.Ioi p, |t r - t p| :=
        Finset.prod_le_prod₀ (fun r hr => hq0)
          (fun r hr => ht p r (ne_of_lt (Finset.mem_Ioi.mp hr)))
  have hprod : q ^ (m * m) ≤ ∏ p : Fin m, ∏ r ∈ Finset.Ioi p, |t r - t p| := by
    calc
      q ^ (m * m) = ∏ _p : Fin m, q ^ m := by simp [pow_mul]
      _ ≤ ∏ p : Fin m, ∏ r ∈ Finset.Ioi p, |t r - t p| :=
        Finset.prod_le_prod₀ (fun p hp => pow_nonneg hq0 _) (fun p hp => htp p)
  apply div_le_div_of_nonneg_right _ (Finset.prod_nonneg fun k hk => Nat.cast_nonneg _)
  rw [pow_add]
  exact mul_le_mul hwp hprod (pow_nonneg hq0 _) (Finset.prod_nonneg fun p hp => abs_nonneg _)

end Submission.Obl.k4_matching_endpoint_volume
