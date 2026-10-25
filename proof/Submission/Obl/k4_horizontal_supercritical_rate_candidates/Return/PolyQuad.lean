import Mathlib

/-!
# Two-variable quadratics as quadratics in the second variable

For `P` of total degree at most two, `eval ![t, y] P = a₀(t) + a₁(t) y + a₂ y^2`, with
explicit coefficient sums over the support.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MvPolynomial Finset

noncomputable section

/-- Coefficient of `y^k` in `P(t, y)`. -/
def ycoef (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ P.support.filter (fun m => m 1 = k), P.coeff m * t ^ (m 0)

theorem fin2_sum (m : Fin 2 →₀ ℕ) : (m.sum fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]

theorem deg_le_of_mem {P : MvPolynomial (Fin 2) ℝ} {m : Fin 2 →₀ ℕ} (hm : m ∈ P.support) :
    m 0 + m 1 ≤ P.totalDegree := by
  have h1 := le_totalDegree hm
  rwa [fin2_sum] at h1

theorem eval_eq_ysum (P : MvPolynomial (Fin 2) ℝ) (t y : ℝ) :
    eval ![t, y] P = ∑ m ∈ P.support, P.coeff m * t ^ (m 0) * y ^ (m 1) := by
  rw [eval_eq']
  apply sum_congr rfl
  intro m _
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem eval_eq_quad (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (t y : ℝ) :
    eval ![t, y] P = ycoef P 0 t + ycoef P 1 t * y + ycoef P 2 t * y ^ 2 := by
  classical
  rw [eval_eq_ysum]
  have hdeg : ∀ m ∈ P.support, m 1 ≤ 2 := by
    intro m hm
    have := deg_le_of_mem hm
    omega
  have hsplit : P.support = P.support.filter (fun m => m 1 = 0) ∪
      (P.support.filter (fun m => m 1 = 1) ∪ P.support.filter (fun m => m 1 = 2)) := by
    ext m
    simp only [mem_union, mem_filter]
    constructor
    · intro hm
      have := hdeg m hm
      rcases (show m 1 = 0 ∨ m 1 = 1 ∨ m 1 = 2 by omega) with h | h | h
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr (Or.inl ⟨hm, h⟩)
      · exact Or.inr (Or.inr ⟨hm, h⟩)
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have e0 : ∑ m ∈ P.support.filter (fun m => m 1 = 0), P.coeff m * t ^ (m 0) * y ^ (m 1) =
      ycoef P 0 t := by
    unfold ycoef; apply sum_congr rfl; intro m hm; rw [(mem_filter.mp hm).2]; ring
  have e1 : ∑ m ∈ P.support.filter (fun m => m 1 = 1), P.coeff m * t ^ (m 0) * y ^ (m 1) =
      ycoef P 1 t * y := by
    unfold ycoef; rw [sum_mul]; apply sum_congr rfl; intro m hm; rw [(mem_filter.mp hm).2]; ring
  have e2 : ∑ m ∈ P.support.filter (fun m => m 1 = 2), P.coeff m * t ^ (m 0) * y ^ (m 1) =
      ycoef P 2 t * y ^ 2 := by
    unfold ycoef; rw [sum_mul]; apply sum_congr rfl; intro m hm; rw [(mem_filter.mp hm).2]
  rw [hsplit, sum_union, sum_union, e0, e1, e2]
  · ring
  · rw [disjoint_filter]; intro m _ h1 h2; omega
  · rw [disjoint_union_right]
    constructor <;> (rw [disjoint_filter]; intro m _ h1 h2; omega)

/-- The `y^2` coefficient does not depend on `t`. -/
theorem ycoef_two_const (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (t t' : ℝ) :
    ycoef P 2 t = ycoef P 2 t' := by
  unfold ycoef
  apply sum_congr rfl
  intro m hm
  obtain ⟨hm, hm1⟩ := mem_filter.mp hm
  have h1 := deg_le_of_mem hm
  have : m 0 = 0 := by omega
  rw [this, pow_zero, pow_zero]

/-- The `y` coefficient is affine in `t`: its change is bounded by the support size times
the coefficient bound times `|t - t'|`. -/
theorem abs_ycoef_one_sub_le (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {B : ℝ}
    (hB : ∀ m, |P.coeff m| ≤ B) (t t' : ℝ) :
    |ycoef P 1 t - ycoef P 1 t'| ≤ (P.support.card : ℝ) * B * |t - t'| := by
  classical
  unfold ycoef
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ m ∈ P.support.filter (fun m => m 1 = 1), |P.coeff m * t ^ m 0 - P.coeff m * t' ^ m 0|
      ≤ ∑ _m ∈ P.support.filter (fun m => m 1 = 1), B * |t - t'| := by
        apply sum_le_sum
        intro m hm
        obtain ⟨hm, hm1⟩ := mem_filter.mp hm
        have h1 := deg_le_of_mem hm
        have hm0 : m 0 ≤ 1 := by omega
        rw [← mul_sub, abs_mul]
        interval_cases h : m 0
        · simp only [pow_zero, sub_self, abs_zero, mul_zero]
          exact mul_nonneg ((abs_nonneg _).trans (hB m)) (abs_nonneg _)
        · simp only [pow_one]; exact mul_le_mul_of_nonneg_right (hB m) (abs_nonneg _)
    _ = ((P.support.filter (fun m => m 1 = 1)).card : ℝ) * (B * |t - t'|) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (P.support.card : ℝ) * B * |t - t'| := by
        have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
        rw [mul_assoc]
        gcongr
        exact filter_subset _ _

/-- Each `y`-coefficient is Lipschitz in `t ∈ [-1, 1]`. -/
theorem abs_ycoef_sub_le (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {B : ℝ}
    (hB : ∀ m, |P.coeff m| ≤ B) (k : ℕ) {t t' : ℝ} (ht : |t| ≤ 1) (ht' : |t'| ≤ 1) :
    |ycoef P k t - ycoef P k t'| ≤ (P.support.card : ℝ) * B * (2 * |t - t'|) := by
  classical
  unfold ycoef
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  calc ∑ m ∈ P.support.filter (fun m => m 1 = k), |P.coeff m * t ^ m 0 - P.coeff m * t' ^ m 0|
      ≤ ∑ _m ∈ P.support.filter (fun m => m 1 = k), B * (2 * |t - t'|) := by
        apply sum_le_sum
        intro m hm
        obtain ⟨hm, _⟩ := mem_filter.mp hm
        have h1 := deg_le_of_mem hm
        have hm0 : m 0 ≤ 2 := by omega
        rw [← mul_sub, abs_mul]
        refine mul_le_mul (hB m) ?_ (abs_nonneg _) hB0
        interval_cases h : m 0
        · simp only [pow_zero, sub_self, abs_zero]; positivity
        · simp only [pow_one]; linarith [abs_nonneg (t - t')]
        · have : t ^ 2 - t' ^ 2 = (t - t') * (t + t') := by ring
          rw [this, abs_mul]
          have : |t + t'| ≤ 2 := (abs_add_le _ _).trans (by linarith)
          nlinarith [abs_nonneg (t - t')]
    _ = ((P.support.filter (fun m => m 1 = k)).card : ℝ) * (B * (2 * |t - t'|)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (P.support.card : ℝ) * B * (2 * |t - t'|) := by
        rw [mul_assoc]
        gcongr
        exact filter_subset _ _

/-- Size of each `y`-coefficient for `|t| ≤ 1`. -/
theorem abs_ycoef_le (P : MvPolynomial (Fin 2) ℝ) {B : ℝ} (hB : ∀ m, |P.coeff m| ≤ B) (k : ℕ)
    {t : ℝ} (ht : |t| ≤ 1) : |ycoef P k t| ≤ (P.support.card : ℝ) * B := by
  classical
  unfold ycoef
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  calc ∑ m ∈ P.support.filter (fun m => m 1 = k), |P.coeff m * t ^ m 0|
      ≤ ∑ _m ∈ P.support.filter (fun m => m 1 = k), B := by
        apply sum_le_sum
        intro m _
        rw [abs_mul, abs_pow]
        have : |t| ^ m 0 ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
        nlinarith [hB m, abs_nonneg (P.coeff m)]
    _ = ((P.support.filter (fun m => m 1 = k)).card : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (P.support.card : ℝ) * B := by
        gcongr
        exact filter_subset _ _

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
