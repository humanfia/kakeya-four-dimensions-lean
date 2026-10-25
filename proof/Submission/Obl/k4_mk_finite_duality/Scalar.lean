import Mathlib

open scoped BigOperators

namespace Submission.Obl.k4_mk_finite_duality

/-- Finite Hölder with `n` equal exponents, including zero rows. -/
theorem finite_holder {n m : ℕ} (hn : 0 < n) (H : Fin n → Fin m → ℝ)
    (hH : ∀ i q, 0 ≤ H i q) :
    (∑ q, (∏ i, H i q) ^ (1 / (n : ℝ))) ≤
      (∏ i, ∑ q, H i q) ^ (1 / (n : ℝ)) := by
  classical
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : ∀ i, 0 ≤ ∑ q, H i q := fun i => Finset.sum_nonneg (fun q _ => hH i q)
  by_cases hpos : ∀ i, 0 < ∑ q, H i q
  · let B : Fin n → ℝ := fun i => ∑ q, H i q
    have hB : ∀ i, 0 < B i := hpos
    have hBP : 0 < ∏ i, B i := Finset.prod_pos (fun i _ => hB i)
    have hratio : ∀ i q, 0 ≤ H i q / B i := fun i q =>
      div_nonneg (hH i q) (hB i).le
    have hsplit : ∀ q,
        (∏ i, H i q) ^ (1 / (n : ℝ)) =
          (∏ i, B i) ^ (1 / (n : ℝ)) *
            ∏ i, (H i q / B i) ^ (1 / (n : ℝ)) := by
      intro q
      rw [Real.finsetProd_rpow _ _ (fun i _ => hratio i q),
        ← Real.mul_rpow hBP.le (Finset.prod_nonneg (fun i _ => hratio i q))]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      exact (mul_div_cancel₀ (H i q) (hB i).ne').symm
    have hpoint : ∀ q,
        (∏ i, (H i q / B i) ^ (1 / (n : ℝ))) ≤
          ∑ i, (1 / (n : ℝ)) * (H i q / B i) := by
      intro q
      exact Real.geom_mean_le_arith_mean_weighted Finset.univ
        (fun _ : Fin n => 1 / (n : ℝ)) (fun i => H i q / B i)
        (fun _ _ => by positivity) (by simp [hnR.ne']) (fun i _ => hratio i q)
    calc
      (∑ q, (∏ i, H i q) ^ (1 / (n : ℝ))) =
          (∏ i, B i) ^ (1 / (n : ℝ)) *
            ∑ q, ∏ i, (H i q / B i) ^ (1 / (n : ℝ)) := by
              simp_rw [hsplit]
              rw [Finset.mul_sum]
      _ ≤ (∏ i, B i) ^ (1 / (n : ℝ)) *
          ∑ q, ∑ i, (1 / (n : ℝ)) * (H i q / B i) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hpoint q))
              (Real.rpow_nonneg hBP.le _)
      _ = (∏ i, B i) ^ (1 / (n : ℝ)) := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, ← Finset.sum_div]
        simp [B, (hB _).ne', hnR.ne']
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have hi0 : ∑ q, H i q = 0 := le_antisymm hi (hs i)
    have hrow : ∀ q, H i q = 0 := fun q =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hH i q)).mp hi0 q (Finset.mem_univ q)
    have hp : ∀ q, ∏ j, H j q = 0 := fun q =>
      Finset.prod_eq_zero (Finset.mem_univ i) (hrow q)
    simp_rw [hp, Real.zero_rpow (one_div_ne_zero hnR.ne'), Finset.sum_const_zero]
    exact Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hs i)) _

/-- A normalized-demand factorization implies the finite multilinear bound. -/
theorem finite_duality_scalar {n m : ℕ} (hn : 2 ≤ n)
    (F : Fin m → ℝ) (hF : ∀ q, 0 ≤ F q)
    (C : Fin n → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hfactor : ∀ M : Fin m → ℝ, (∀ q, 0 ≤ M q) → (∑ q, M q) = 1 →
      ∃ H : Fin n → Fin m → ℝ, (∀ i q, 0 ≤ H i q) ∧
        (∀ q, M q * F q ≤ ∏ i, H i q) ∧ (∀ i, (∑ q, H i q) ≤ C i)) :
    (∑ q, F q ^ (1 / ((n : ℝ) - 1))) ≤
      (∏ i, C i) ^ (1 / ((n : ℝ) - 1)) := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hn1 : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let p : ℝ := 1 / ((n : ℝ) - 1)
  let S : ℝ := ∑ q, F q ^ p
  have hp : 0 < p := one_div_pos.mpr hn1
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun q _ => Real.rpow_nonneg (hF q) _)
  have hCP : 0 ≤ ∏ i, C i := Finset.prod_nonneg (fun i _ => hC i)
  change S ≤ (∏ i, C i) ^ p
  by_cases hS : S = 0
  · rw [hS]
    exact Real.rpow_nonneg hCP _
  have hS : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
  let M : Fin m → ℝ := fun q => F q ^ p / S
  have hM : ∀ q, 0 ≤ M q := fun q => div_nonneg (Real.rpow_nonneg (hF q) _) hS.le
  have hMsum : (∑ q, M q) = 1 := by
    simp only [M, ← Finset.sum_div]
    exact div_self hS.ne'
  obtain ⟨H, hH, hpoint, hsum⟩ := hfactor M hM hMsum
  have hexponent : (p + 1) * (1 / (n : ℝ)) = p := by
    dsimp [p]
    field_simp
    ring
  have hroot : ∀ q, (M q * F q) ^ (1 / (n : ℝ)) =
      F q ^ p / S ^ (1 / (n : ℝ)) := by
    intro q
    change (F q ^ p / S * F q) ^ (1 / (n : ℝ)) = _
    rw [div_mul_eq_mul_div, Real.div_rpow
      (mul_nonneg (Real.rpow_nonneg (hF q) _) (hF q)) hS.le]
    congr 1
    rw [← Real.rpow_add_one' (hF q) (by linarith : p + 1 ≠ 0),
      ← Real.rpow_mul (hF q), hexponent]
  have hbound : S / S ^ (1 / (n : ℝ)) ≤ (∏ i, C i) ^ (1 / (n : ℝ)) := by
    calc
      S / S ^ (1 / (n : ℝ)) = ∑ q, (M q * F q) ^ (1 / (n : ℝ)) := by
        simp_rw [hroot]
        exact Finset.sum_div _ _ _
      _ ≤ ∑ q, (∏ i, H i q) ^ (1 / (n : ℝ)) :=
        Finset.sum_le_sum (fun q _ => Real.rpow_le_rpow
          (mul_nonneg (hM q) (hF q)) (hpoint q) (by positivity))
      _ ≤ (∏ i, ∑ q, H i q) ^ (1 / (n : ℝ)) := finite_holder hn0 H hH
      _ ≤ (∏ i, C i) ^ (1 / (n : ℝ)) := Real.rpow_le_rpow
        (Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun q _ => hH i q)))
        (Finset.prod_le_prod₀
          (fun i _ => Finset.sum_nonneg (fun q _ => hH i q)) (fun i _ => hsum i))
        (by positivity)
  have hpown := pow_le_pow_left₀
    (div_nonneg hS.le (Real.rpow_nonneg hS.le _)) hbound n
  rw [div_pow, one_div,
    Real.rpow_inv_natCast_pow hS.le (by omega),
    Real.rpow_inv_natCast_pow hCP (by omega)] at hpown
  have hpoweq : S ^ n = S ^ (n - 1) * S := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpoweq, mul_div_cancel_right₀ _ hS.ne'] at hpown
  have hpNat : p = ((n - 1 : ℕ) : ℝ)⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    simp [p]
  have hfinal := Real.rpow_le_rpow (pow_nonneg hS.le _) hpown hp.le
  rw [hpNat] at hfinal ⊢
  rw [Real.pow_rpow_inv_natCast hS.le (show n - 1 ≠ 0 by omega)] at hfinal
  exact hfinal

/-- Rewrite the product of line budgets into the constant and family masses. -/
theorem budget_product {n : ℕ} (K : ℝ) (hK : 0 ≤ K) (W : Fin n → ℝ)
    (hW : ∀ i, 0 ≤ W i) :
    (∏ i, K * W i) ^ (1 / ((n : ℝ) - 1)) =
      K ^ ((n : ℝ) / ((n : ℝ) - 1)) *
        ∏ i, W i ^ (1 / ((n : ℝ) - 1)) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Real.mul_rpow (pow_nonneg hK n) (Finset.prod_nonneg (fun i _ => hW i)),
    ← Real.rpow_natCast_mul hK, Real.finsetProd_rpow _ _ (fun i _ => hW i)]
  congr 2
  ring

end Submission.Obl.k4_mk_finite_duality
