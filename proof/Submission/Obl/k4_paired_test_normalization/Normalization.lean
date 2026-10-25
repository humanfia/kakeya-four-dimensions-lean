-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/Normalization.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.Rescaling

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial

/-- The coefficient l1 size is used only to choose one constant for a label. -/
noncomputable def coefficientSize {σ : Type*} (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ P.support, |P.coeff m|

theorem coefficientSize_nonneg {σ : Type*} (P : MvPolynomial σ ℝ) :
    0 ≤ coefficientSize P := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem abs_coeff_le_coefficientSize {σ : Type*} (P : MvPolynomial σ ℝ) (m) :
    |P.coeff m| ≤ coefficientSize P := by
  classical
  by_cases hm : m ∈ P.support
  · exact Finset.single_le_sum (f := fun m => |P.coeff m|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.mp hm, abs_zero]
    exact coefficientSize_nonneg P

/-- On the unit coordinate box, coefficient size controls evaluation. -/
theorem abs_eval_le_coefficientSize {σ : Type*} (P : MvPolynomial σ ℝ)
    (z : σ → ℝ) (hz : ∀ i, |z i| ≤ 1) : |eval z P| ≤ coefficientSize P := by
  classical
  have hmon (m : σ →₀ ℕ) : |eval z (monomial m (P.coeff m))| ≤ |P.coeff m| := by
    rw [eval_monomial, abs_mul]
    have hprod : |m.prod (fun i e => z i ^ e)| ≤ 1 := by
      calc
        |m.prod (fun i e => z i ^ e)| = ∏ i ∈ m.support, |z i| ^ m i := by
          simp [Finsupp.prod, Finset.abs_prod]
        _ ≤ ∏ _i ∈ m.support, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => pow_le_one₀ (abs_nonneg _) (hz i))
        _ = 1 := by simp
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (abs_nonneg (P.coeff m))
  conv_lhs => rw [P.as_sum]
  rw [eval_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => hmon m))

/-- Downward equation scaling can put every discriminant coefficient below one,
while retaining a definite fraction of its original coefficient size. -/
theorem exists_discriminant_normalization (P : MvPolynomial (Fin 4) ℝ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (∀ m, |(disc (C t * P)).coeff m| ≤ 1) ∧
      (min (coefficientSize (disc P)) 1) / 2 ≤ coefficientSize (disc (C t * P)) := by
  classical
  let A := coefficientSize (disc P)
  have hA : 0 ≤ A := coefficientSize_nonneg _
  have hAp : 0 < 1 + A := by linarith
  let t := (Real.sqrt (1 + A))⁻¹
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hAp)
  have hsq : t ^ 2 = (1 + A)⁻¹ := by
    dsimp [t]
    rw [inv_pow, Real.sq_sqrt hAp.le]
  have ht1 : t ≤ 1 := by
    apply (inv_le_one₀ (Real.sqrt_pos.mpr hAp)).mpr
    apply Real.le_sqrt_of_sq_le
    nlinarith
  refine ⟨t, ht, ht1, ?_, ?_⟩
  · intro m
    rw [abs_disc_coeff_C_mul, hsq]
    have hc : |(disc P).coeff m| ≤ 1 + A := by
      have := abs_coeff_le_coefficientSize (disc P) m
      dsimp [A] at *
      linarith
    calc
      (1 + A)⁻¹ * |(disc P).coeff m| ≤ (1 + A)⁻¹ * (1 + A) :=
        mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hAp.le)
      _ = 1 := inv_mul_cancel₀ hAp.ne'
  · have hsupport : (disc (C t * P)).support = (disc P).support := by
      rw [disc_C_mul]
      ext m
      simp only [mem_support_iff, coeff_C_mul, mul_ne_zero_iff]
      simp [ht.ne']
    change min A 1 / 2 ≤ ∑ m ∈ (disc (C t * P)).support, |(disc (C t * P)).coeff m|
    rw [hsupport]
    simp_rw [abs_disc_coeff_C_mul]
    rw [← Finset.mul_sum]
    change min A 1 / 2 ≤ t ^ 2 * A
    rw [hsq, inv_mul_eq_div]
    apply (le_div_iff₀ hAp).mpr
    by_cases hA1 : A ≤ 1
    · rw [min_eq_left hA1]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hA1)]
    · rw [min_eq_right (le_of_not_ge hA1)]
      nlinarith

end Submission.Obl.k4_paired_test_normalization
