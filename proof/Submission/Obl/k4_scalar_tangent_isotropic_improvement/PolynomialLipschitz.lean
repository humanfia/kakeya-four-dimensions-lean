import Submission.Obl.k4_scalar_tangent_isotropic_improvement.LinePolynomials

/-! Coefficient bounds control polynomial values and their variation on bounded boxes. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open MvPolynomial
open scoped BigOperators

theorem binary_exponents_sum (b : Fin 2 →₀ ℕ) : b.sum (fun _ n => n) = b 0 + b 1 := by
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · simp

theorem binary_support_card_le (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) : p.support.card ≤ (D + 1) ^ 2 := by
  classical
  have hcard := Finset.card_le_card_of_injOn (s := p.support)
    (t := (Finset.range (D + 1)).product (Finset.range (D + 1)))
    (fun b => (b 0, b 1)) (by
      intro b hb
      have hdeg := (le_totalDegree hb).trans hp
      rw [binary_exponents_sum] at hdeg
      change (b 0, b 1) ∈ (Finset.range (D + 1)).product (Finset.range (D + 1))
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩) (by
      intro b hb c hc he
      ext i
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he)
  simpa [pow_two] using hcard

theorem pow_abs_le_of_bounded {a R : ℝ} {n D : ℕ}
    (hR : 1 ≤ R) (ha : |a| ≤ R) (hn : n ≤ D) : |a ^ n| ≤ R ^ D := by
  rw [abs_pow]
  exact (pow_le_pow_left₀ (abs_nonneg _) ha n).trans (pow_le_pow_right₀ hR hn)

theorem pow_lipschitz_of_bounded {a b R : ℝ} {n D : ℕ}
    (hR : 1 ≤ R) (ha : |a| ≤ R) (hb : |b| ≤ R) (hn : n ≤ D) :
    |a ^ n - b ^ n| ≤ |a - b| * ((D : ℝ) + 1) * R ^ D := by
  calc
    |a ^ n - b ^ n| ≤ |a - b| * (n : ℝ) * max |a| |b| ^ (n - 1) :=
      abs_pow_sub_pow_le a b n
    _ ≤ |a - b| * ((D : ℝ) + 1) * R ^ D := by
      gcongr
      · exact_mod_cast Nat.le_succ_of_le hn
      · exact (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) (max_le ha hb) _).trans
          (pow_le_pow_right₀ hR (by omega))

theorem binary_monomial_lipschitz {D a b : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (ha : a ≤ D) (hb : b ≤ D)
    (x y : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    |x 0 ^ a * x 1 ^ b - y 0 ^ a * y 1 ^ b| ≤
      2 * ((D : ℝ) + 1) * R ^ (2 * D) * dist x y := by
  have hd (i : Fin 2) : |x i - y i| ≤ dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y i
  have h0 : |x 0 ^ a - y 0 ^ a| ≤ dist x y * ((D : ℝ) + 1) * R ^ D :=
    (pow_lipschitz_of_bounded hR (hx 0) (hy 0) ha).trans (by gcongr; exact hd 0)
  have h1 : |x 1 ^ b - y 1 ^ b| ≤ dist x y * ((D : ℝ) + 1) * R ^ D :=
    (pow_lipschitz_of_bounded hR (hx 1) (hy 1) hb).trans (by gcongr; exact hd 1)
  calc
    |x 0 ^ a * x 1 ^ b - y 0 ^ a * y 1 ^ b| =
        |(x 0 ^ a - y 0 ^ a) * x 1 ^ b + y 0 ^ a * (x 1 ^ b - y 1 ^ b)| := by
      congr 1
      ring
    _ ≤ |x 0 ^ a - y 0 ^ a| * |x 1 ^ b| + |y 0 ^ a| * |x 1 ^ b - y 1 ^ b| := by
      simpa only [abs_mul] using abs_add_le ((x 0 ^ a - y 0 ^ a) * x 1 ^ b)
        (y 0 ^ a * (x 1 ^ b - y 1 ^ b))
    _ ≤ (dist x y * ((D : ℝ) + 1) * R ^ D) * R ^ D +
        R ^ D * (dist x y * ((D : ℝ) + 1) * R ^ D) := by
      apply add_le_add
      · exact mul_le_mul h0 (pow_abs_le_of_bounded hR (hx 1) hb) (abs_nonneg _) (by positivity)
      · exact mul_le_mul (pow_abs_le_of_bounded hR (hy 0) ha) h1 (abs_nonneg _)
          (pow_nonneg (zero_le_one.trans hR) _)
    _ = _ := by rw [pow_mul]; ring

theorem binary_polynomial_eval_bound (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    {B R : ℝ} (hp : p.totalDegree ≤ D) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hc : ∀ b, |p.coeff b| ≤ B) (x : Fin 2 → ℝ) (hx : ∀ i, |x i| ≤ R) :
    |eval x p| ≤ ((D : ℝ) + 1) ^ 2 * B * R ^ (2 * D) := by
  classical
  rw [eval_eq']
  calc
    |∑ b ∈ p.support, p.coeff b * ∏ i, x i ^ b i| ≤
        ∑ b ∈ p.support, |p.coeff b * ∏ i, x i ^ b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ p.support, B * R ^ (2 * D) := by
      apply Finset.sum_le_sum
      intro b hb
      have hdeg := (le_totalDegree hb).trans hp
      rw [binary_exponents_sum] at hdeg
      simp only [Fin.prod_univ_two, abs_mul]
      calc
        |p.coeff b| * (|x 0 ^ b 0| * |x 1 ^ b 1|) ≤ B * (R ^ D * R ^ D) := by
          gcongr
          · exact hc b
          · exact pow_abs_le_of_bounded hR (hx 0) (by omega)
          · exact pow_abs_le_of_bounded hR (hx 1) (by omega)
        _ = _ := by rw [pow_mul]; ring
    _ ≤ ((D : ℝ) + 1) ^ 2 * B * R ^ (2 * D) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (p.support.card : ℝ) ≤ ((D : ℝ) + 1) ^ 2 := by
        exact_mod_cast binary_support_card_le p D hp
      calc
        (p.support.card : ℝ) * (B * R ^ (2 * D)) ≤
          (((D : ℝ) + 1) ^ 2) * (B * R ^ (2 * D)) := by gcongr
        _ = _ := by ring

theorem binary_polynomial_lipschitz (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    {B R : ℝ} (hp : p.totalDegree ≤ D) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hc : ∀ b, |p.coeff b| ≤ B) (x y : Fin 2 → ℝ)
    (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    |eval x p - eval y p| ≤ 2 * ((D : ℝ) + 1) ^ 3 * B * R ^ (2 * D) * dist x y := by
  classical
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib]
  calc
    |∑ b ∈ p.support, (p.coeff b * ∏ i, x i ^ b i - p.coeff b * ∏ i, y i ^ b i)| ≤
      ∑ b ∈ p.support, |p.coeff b * ∏ i, x i ^ b i - p.coeff b * ∏ i, y i ^ b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ p.support, B * (2 * ((D : ℝ) + 1) * R ^ (2 * D) * dist x y) := by
      apply Finset.sum_le_sum
      intro b hb
      have hdeg := (le_totalDegree hb).trans hp
      rw [binary_exponents_sum] at hdeg
      rw [← mul_sub, abs_mul]
      simp only [Fin.prod_univ_two]
      exact mul_le_mul (hc b) (binary_monomial_lipschitz hR (by omega) (by omega) x y hx hy)
        (abs_nonneg _) hB
    _ ≤ 2 * ((D : ℝ) + 1) ^ 3 * B * R ^ (2 * D) * dist x y := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : (p.support.card : ℝ) ≤ ((D : ℝ) + 1) ^ 2 := by
        exact_mod_cast binary_support_card_le p D hp
      calc
        (p.support.card : ℝ) * (B * (2 * ((D : ℝ) + 1) * R ^ (2 * D) * dist x y)) ≤
          (((D : ℝ) + 1) ^ 2) * (B * (2 * ((D : ℝ) + 1) * R ^ (2 * D) * dist x y)) := by
            gcongr
        _ = _ := by ring

theorem pderiv_coefficients_bound (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    {H : ℝ} (hp : p.totalDegree ≤ D) (hH : 0 ≤ H) (hc : ∀ b, |p.coeff b| ≤ H)
    (i : Fin 2) (b : Fin 2 →₀ ℕ) :
    |(pderiv i p).coeff b| ≤ ((D : ℝ) + 1) * H := by
  rw [coeff_pderiv]
  by_cases hz : p.coeff (b + Finsupp.single i 1) = 0
  · simp only [hz, zero_mul, abs_zero]
    positivity
  have hdeg := (le_totalDegree (mem_support_iff.mpr hz)).trans hp
  rw [binary_exponents_sum] at hdeg
  have hbi : b i ≤ D := by
    fin_cases i <;> simp at hdeg ⊢ <;> omega
  have hf : |(b i : ℝ) + 1| ≤ (D : ℝ) + 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.succ_le_succ hbi
  rw [abs_mul]
  calc
    |p.coeff (b + Finsupp.single i 1)| * |(b i : ℝ) + 1| ≤ H * ((D : ℝ) + 1) :=
      mul_le_mul (hc _) hf (abs_nonneg _) hH
    _ = _ := mul_comm _ _

theorem thirdPartials_coefficients_bound (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    {H : ℝ} (hp : p.totalDegree ≤ D) (hH : 0 ≤ H) (hc : ∀ b, |p.coeff b| ≤ H)
    (j : Fin 4) (b : Fin 2 →₀ ℕ) :
    |(thirdPartials p j).coeff b| ≤ ((D : ℝ) + 1) ^ 3 * H := by
  have hd (q : MvPolynomial (Fin 2) ℝ) (i : Fin 2) (hq : q.totalDegree ≤ D) :
      (pderiv i q).totalDegree ≤ D :=
    (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le q i).trans
      ((Nat.sub_le _ _).trans hq)
  have h1 (i : Fin 2) : ∀ b, |(pderiv i p).coeff b| ≤ ((D : ℝ) + 1) * H :=
    pderiv_coefficients_bound p D hp hH hc i
  have h2 (i j : Fin 2) : ∀ b, |(pderiv i (pderiv j p)).coeff b| ≤
      ((D : ℝ) + 1) * (((D : ℝ) + 1) * H) :=
    pderiv_coefficients_bound _ D (hd p j hp) (by positivity) (h1 j) i
  have h3 (i j k : Fin 2) : |(pderiv i (pderiv j (pderiv k p))).coeff b| ≤
      ((D : ℝ) + 1) ^ 3 * H := by
    have h := pderiv_coefficients_bound _ D (hd _ j (hd p k hp)) (by positivity) (h2 j k) i b
    convert h using 1 <;> ring
  fin_cases j
  · exact h3 0 0 0
  · exact h3 0 0 1
  · exact h3 0 1 1
  · exact h3 1 1 1

theorem cubicTest_lipschitz (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    {B R v w : ℝ} (hp : p.totalDegree ≤ D) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hc : ∀ b, |p.coeff b| ≤ B) (x y : Fin 2 → ℝ)
    (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) (hv : |v| ≤ R) (hw : |w| ≤ R) :
    |cubicTest p x v - cubicTest p y w| ≤
      (16 * (2 * ((D : ℝ) + 1) ^ 6 + 4 * ((D : ℝ) + 1) ^ 5)) *
        B * R ^ (2 * D + 3) * (dist x y + |v - w|) := by
  classical
  let U : ℝ := ((D : ℝ) + 1) ^ 5 * B * R ^ (2 * D)
  let L : ℝ := 2 * ((D : ℝ) + 1) ^ 6 * B * R ^ (2 * D)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hval (j : Fin 4) : |eval y (thirdPartials p j)| ≤ U := by
    have h := binary_polynomial_eval_bound (thirdPartials p j) D
      ((totalDegree_thirdPartials_le p j).trans hp) (by positivity) hR
      (thirdPartials_coefficients_bound p D hp hB hc j) y hy
    convert h using 1 <;> dsimp [U] <;> ring
  have hvar (j : Fin 4) :
      |eval x (thirdPartials p j) - eval y (thirdPartials p j)| ≤ L * dist x y := by
    have h := binary_polynomial_lipschitz (thirdPartials p j) D
      ((totalDegree_thirdPartials_le p j).trans hp) (by positivity) hR
      (thirdPartials_coefficients_bound p D hp hB hc j) x y hx hy
    convert h using 1 <;> dsimp [L] <;> ring
  have hterm (j : Fin 4) :
      |((3 : ℕ).choose (j : ℕ) : ℝ) * eval x (thirdPartials p j) * v ^ (j : ℕ) -
        ((3 : ℕ).choose (j : ℕ) : ℝ) * eval y (thirdPartials p j) * w ^ (j : ℕ)| ≤
      4 * R ^ 3 * (L + 4 * U) * (dist x y + |v - w|) := by
    have hj : (j : ℕ) ≤ 3 := by omega
    have hbin : |((3 : ℕ).choose (j : ℕ) : ℝ)| ≤ 4 := by fin_cases j <;> norm_num
    have hpv := pow_abs_le_of_bounded hR hv hj
    have hpvw := pow_lipschitz_of_bounded hR hv hw hj
    norm_num at hpvw
    calc
      _ = |((3 : ℕ).choose (j : ℕ) : ℝ) *
          (v ^ (j : ℕ) * (eval x (thirdPartials p j) - eval y (thirdPartials p j)) +
            (v ^ (j : ℕ) - w ^ (j : ℕ)) * eval y (thirdPartials p j))| := by
        congr 1
        ring
      _ ≤ 4 * (R ^ 3 * (L * dist x y) + (|v - w| * 4 * R ^ 3) * U) := by
        rw [abs_mul]
        apply mul_le_mul hbin _ (abs_nonneg _) (by norm_num)
        calc
          _ ≤ |v ^ (j : ℕ)| * |eval x (thirdPartials p j) - eval y (thirdPartials p j)| +
              |v ^ (j : ℕ) - w ^ (j : ℕ)| * |eval y (thirdPartials p j)| := by
            simpa only [abs_mul] using abs_add_le
              (v ^ (j : ℕ) * (eval x (thirdPartials p j) - eval y (thirdPartials p j)))
              ((v ^ (j : ℕ) - w ^ (j : ℕ)) * eval y (thirdPartials p j))
          _ ≤ _ := add_le_add
            (mul_le_mul hpv (hvar j) (abs_nonneg _) (by positivity))
            (mul_le_mul hpvw (hval j) (abs_nonneg _) (by positivity))
      _ ≤ 4 * R ^ 3 * (L + 4 * U) * (dist x y + |v - w|) := by
        have hcross : 0 ≤ L * |v - w| + 4 * U * dist x y := by positivity
        nlinarith [mul_nonneg (show 0 ≤ 4 * R ^ 3 by positivity) hcross]
  rw [cubicTest, cubicTest, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin 4, |((3 : ℕ).choose (j : ℕ) : ℝ) * eval x (thirdPartials p j) * v ^ (j : ℕ) -
        ((3 : ℕ).choose (j : ℕ) : ℝ) * eval y (thirdPartials p j) * w ^ (j : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 4, 4 * R ^ 3 * (L + 4 * U) * (dist x y + |v - w|) :=
      Finset.sum_le_sum (fun j hj => hterm j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [L, U]
      rw [pow_add]
      ring

theorem exists_cubicTest_lipschitz (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (H v w : ℝ) (x y : Fin 2 → ℝ),
      p.totalDegree ≤ D → 1 ≤ H → (∀ b, |p.coeff b| ≤ H) →
      (∀ i, |x i| ≤ H) → (∀ i, |y i| ≤ H) → |v| ≤ H → |w| ≤ H →
      |cubicTest p x v - cubicTest p y w| ≤
        C * H ^ (2 * D + 4) * (dist x y + |v - w|) := by
  refine ⟨16 * (2 * ((D : ℝ) + 1) ^ 6 + 4 * ((D : ℝ) + 1) ^ 5), by positivity, ?_⟩
  intro p H v w x y hp hH hc hx hy hv hw
  convert cubicTest_lipschitz p D hp (zero_le_one.trans hH) hH hc x y hx hy hv hw using 1
  rw [show 2 * D + 4 = (2 * D + 3) + 1 by omega, pow_succ]
  ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
