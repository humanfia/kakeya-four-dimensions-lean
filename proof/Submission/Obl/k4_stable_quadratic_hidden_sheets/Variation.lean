import Mathlib

namespace Submission.Obl.k4_stable_quadratic_hidden_sheets

open scoped BigOperators

lemma exponent_le_two {p : MvPolynomial (Fin 3) ℝ} (hp : p.totalDegree ≤ 2)
    {e : Fin 3 →₀ ℕ} (he : e ∈ p.support) (i : Fin 3) : e i ≤ 2 := by
  calc
    e i ≤ ∑ j : Fin 3, e j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = e.sum (fun _ k => k) := (Finsupp.sum_fintype e (fun _ k => k) (by simp)).symm
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree he
    _ ≤ 2 := hp

lemma support_card_le {p : MvPolynomial (Fin 3) ℝ} (hp : p.totalDegree ≤ 2) :
    p.support.card ≤ 27 := by
  classical
  let enc : (Fin 3 →₀ ℕ) → (Fin 3 → Fin 3) := fun e i => ⟨e i % 3, Nat.mod_lt _ (by decide)⟩
  have hi : Set.InjOn enc (p.support : Set (Fin 3 →₀ ℕ)) := by
    intro e he d hd hed
    ext i
    have h := congrArg (fun v : Fin 3 → Fin 3 => (v i).val) hed
    dsimp [enc] at h
    simpa [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (exponent_le_two hp he i)),
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le (exponent_le_two hp hd i))] using h
  have hc := Finset.card_le_card_of_injOn enc (by intro e he; exact Finset.mem_univ _) hi
  convert hc using 1
  norm_num [Fintype.card_fun]

/-- Every monomial of total degree at most two has uniform local variation. -/
lemma monomial3_sub_le (i j k : ℕ) (hdeg : i + j + k ≤ 2)
    (R δ : ℝ) (hR : 1 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x y : Fin 3 → ℂ) (hx : ∀ i, ‖x i‖ ≤ R) (hy : ∀ i, ‖y i - x i‖ ≤ δ) :
    ‖y 0 ^ i * y 1 ^ j * y 2 ^ k - x 0 ^ i * x 1 ^ j * x 2 ^ k‖ ≤
      8 * R ^ 2 * δ := by
  have hy' (i) : ‖y i‖ ≤ R + 1 := by
    calc
      ‖y i‖ = ‖(y i - x i) + x i‖ := by rw [sub_add_cancel]
      _ ≤ ‖y i - x i‖ + ‖x i‖ := norm_add_le _ _
      _ ≤ δ + R := add_le_add (hy i) (hx i)
      _ ≤ R + 1 := by linarith
  have hnum : 2 * R + 1 ≤ 8 * R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hvar (i) : ‖y i - x i‖ ≤ 8 * R ^ 2 * δ := by
    apply (hy i).trans
    calc
      δ = 1 * δ := (one_mul _).symm
      _ ≤ 8 * R ^ 2 * δ := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg R]) hδ0
  have hmul (i j) : ‖y i * y j - x i * x j‖ ≤ 8 * R ^ 2 * δ := by
    calc
      ‖y i * y j - x i * x j‖ = ‖(y i - x i) * y j + x i * (y j - x j)‖ := by
        congr 1
        ring
      _ ≤ ‖y i - x i‖ * ‖y j‖ + ‖x i‖ * ‖y j - x j‖ := by
        simpa only [norm_mul] using norm_add_le ((y i - x i) * y j) (x i * (y j - x j))
      _ ≤ δ * (R + 1) + R * δ := by
        gcongr
        · exact hy i
        · exact hy' j
        · exact hx i
        · exact hy j
      _ = (2 * R + 1) * δ := by ring
      _ ≤ 8 * R ^ 2 * δ := mul_le_mul_of_nonneg_right hnum hδ0
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  have hk : k ≤ 2 := by omega
  interval_cases i <;> interval_cases j <;> interval_cases k <;>
    first
    | omega
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hvar 0
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hvar 1
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hvar 2
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hmul 0 0
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hmul 0 1
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hmul 0 2
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hmul 1 1
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hmul 1 2
    | simpa only [pow_zero, pow_one, pow_two, mul_one, one_mul] using hmul 2 2
    | simpa only [pow_zero, mul_one, sub_self, norm_zero] using
        (show (0 : ℝ) ≤ 8 * R ^ 2 * δ by positivity)

/-- A coefficient bound gives an explicit local variation bound for quadratics. -/
theorem eval₂_sub_le (P : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ 2)
    (M : ℝ) (hM : ∀ e, |P.coeff e| ≤ M)
    (R δ : ℝ) (hR : 1 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x y : Fin 3 → ℂ) (hx : ∀ i, ‖x i‖ ≤ R) (hy : ∀ i, ‖y i - x i‖ ≤ δ) :
    ‖MvPolynomial.eval₂ (algebraMap ℝ ℂ) y P -
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) x P‖ ≤ 216 * M * R ^ 2 * δ := by
  classical
  have hM0 : 0 ≤ M := (abs_nonneg (P.coeff 0)).trans (hM 0)
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ P.support, ‖(algebraMap ℝ ℂ) (P.coeff e) * (∏ i, y i ^ e i) -
        (algebraMap ℝ ℂ) (P.coeff e) * ∏ i, x i ^ e i‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ P.support, M * (8 * R ^ 2 * δ) := by
      apply Finset.sum_le_sum
      intro e he
      have hdeg : e 0 + e 1 + e 2 ≤ 2 := by
        have h := (MvPolynomial.le_totalDegree he).trans hP
        rw [Finsupp.sum_fintype e (fun _ k => k) (by simp)] at h
        simpa only [Fin.sum_univ_three] using h
      rw [← mul_sub, norm_mul]
      apply mul_le_mul
      · simpa using hM e
      · simpa only [Fin.prod_univ_three] using monomial3_sub_le (e 0) (e 1) (e 2)
          hdeg R δ hR hδ0 hδ1 x y hx hy
      · positivity
      · exact hM0
    _ = (P.support.card : ℝ) * (M * (8 * R ^ 2 * δ)) := by simp
    _ ≤ 27 * (M * (8 * R ^ 2 * δ)) := by
      gcongr
      exact_mod_cast support_card_le hP
    _ = 216 * M * R ^ 2 * δ := by ring

end Submission.Obl.k4_stable_quadratic_hidden_sheets
