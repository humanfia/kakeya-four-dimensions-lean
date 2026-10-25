import Mathlib
import Submission.Obl.k4_algebraic_sheet_remez.Interpolation
import Submission.Obl.k4_algebraic_sheet_remez.Separated

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set Polynomial MeasureTheory

/-- Separated nodes in the unit interval give a quantitative bound for the
interpolating polynomial at zero. -/
theorem lagrange_eval_zero_bound (q : ℕ) (t : Fin q → ℝ) (g : ℝ → ℝ)
    {δ V : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hV : 0 ≤ V)
    (htI : ∀ i, t i ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ i j, i ≠ j → δ ≤ |t i - t j|)
    (hval : ∀ i, |g (t i)| ≤ V) :
    |(Lagrange.interpolate Finset.univ t (fun i => g (t i))).eval 0| ≤
      (q : ℝ) * (δ⁻¹) ^ q * V := by
  classical
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hbasis (i : Fin q) : |(Lagrange.basis Finset.univ t i).eval 0| ≤ (δ⁻¹) ^ q := by
    rw [Lagrange.basis, Polynomial.eval_prod, Finset.abs_prod]
    calc
      _ ≤ ∏ _j ∈ (Finset.univ.erase i), δ⁻¹ := by
        apply Finset.prod_le_prod₀ (fun j hj => abs_nonneg _)
        intro j hj
        have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
        have hdist := hsep i j hij
        have hinvdist : |t i - t j|⁻¹ ≤ δ⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hδ hdist
        simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X, zero_sub, abs_mul, abs_inv, abs_neg]
        calc
          _ ≤ δ⁻¹ * 1 := mul_le_mul hinvdist
            (by simpa only [abs_of_nonneg (htI j).1] using (htI j).2)
            (abs_nonneg _) (inv_nonneg.mpr hδ.le)
          _ = δ⁻¹ := mul_one _
      _ = (δ⁻¹) ^ (Finset.univ.erase i).card := by simp
      _ ≤ (δ⁻¹) ^ q := by
        apply pow_le_pow_right₀ hinv
        exact (Finset.card_le_card (Finset.erase_subset i Finset.univ)).trans_eq (by simp)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  calc
    _ ≤ ∑ i : Fin q, |g (t i) * (Lagrange.basis Finset.univ t i).eval 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin q, V * (δ⁻¹) ^ q := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hval i) (hbasis i) (abs_nonneg _) hV
    _ = (q : ℝ) * (δ⁻¹) ^ q * V := by simp; ring

/-- A fixed-order interpolation estimate from a positive-length measurable
set, with a remainder that does not depend on the length parameter. -/
theorem slice_interpolation_bound (q : ℕ) {g : ℝ → ℝ} {T η V M : ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hV : 0 ≤ V) (hM : 0 ≤ M)
    (hg : ContDiffOn ℝ q g (Ioo (-2 : ℝ) 2))
    (S : Set ℝ) (hS : S ⊆ Icc (0 : ℝ) T)
    (hmass : ENNReal.ofReal η ≤ volume S) (hval : ∀ s ∈ S, |g s| ≤ V)
    (hderiv : ∀ s ∈ Icc (0 : ℝ) T,
      |iteratedDeriv q g s| ≤ (q.factorial : ℝ) * M * (4 / 5 : ℝ) ^ q) :
    |g 0| ≤ (q : ℝ) * (4 * ((q : ℝ) + 1) / η) ^ q * V + M * (4 / 5 : ℝ) ^ q := by
  classical
  have hmass' : ENNReal.ofReal η ≤ volume (S \ {0}) := by
    simpa only [measure_sdiff_null (measure_singleton (0 : ℝ))] using hmass
  obtain ⟨t, htmono, htS, htsep⟩ := exists_separated_nodes q (S \ {0}) hη hmass'
  have htI (i : Fin q) : t i ∈ Icc (0 : ℝ) T := hS (htS i).1
  have htI1 (i : Fin q) : t i ∈ Icc (0 : ℝ) 1 :=
    ⟨(htI i).1, (htI i).2.trans hT1⟩
  have htpos (i : Fin q) : 0 < t i :=
    lt_of_le_of_ne (htI i).1 (Ne.symm (htS i).2)
  let δ := η / (4 * ((q : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 4 * ((q : ℝ) + 1))).mpr
    linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]
  let p := Lagrange.interpolate Finset.univ t (fun i => g (t i))
  have hpbound : |p.eval 0| ≤ (q : ℝ) * (δ⁻¹) ^ q * V :=
    lagrange_eval_zero_bound q t g hδ hδ1 hV htI1 htsep (fun i => hval _ (htS i).1)
  obtain ⟨ξ, hξ, hrem⟩ := interpolation_remainder_zero q hT hT1 hg t htmono htpos htI
  have hprod : |∏ i, (0 - t i)| ≤ (1 : ℝ) := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one₀ (fun i hi => abs_nonneg _)
    intro i hi
    simpa only [zero_sub, abs_neg, abs_of_nonneg (htI1 i).1] using (htI1 i).2
  have hfac : 0 < (q.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos q
  have herr : |g 0 - p.eval 0| ≤ M * (4 / 5 : ℝ) ^ q := by
    rw [hrem, abs_mul, abs_div, Nat.abs_cast]
    calc
      _ ≤ ((q.factorial : ℝ) * M * (4 / 5 : ℝ) ^ q) / (q.factorial : ℝ) * 1 := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right (hderiv ξ hξ) hfac.le
        · exact hprod
        · positivity
        · positivity
      _ = M * (4 / 5 : ℝ) ^ q := by field_simp
  have htri : |g 0| ≤ |g 0 - p.eval 0| + |p.eval 0| := by
    simpa only [sub_add_cancel] using abs_add_le (g 0 - p.eval 0) (p.eval 0)
  have hδeq : δ⁻¹ = 4 * ((q : ℝ) + 1) / η := by dsimp [δ]; rw [inv_div]
  rw [hδeq] at hpbound
  linarith

end Submission.Obl.k4_algebraic_sheet_remez
