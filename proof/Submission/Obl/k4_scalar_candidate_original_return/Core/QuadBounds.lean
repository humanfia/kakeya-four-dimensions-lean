import Submission.Lib.K4PolynomialRemez

/-!
# Elementary bounds for real quadratic polynomials in two variables
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return.QuadBounds

open MeasureTheory Set MvPolynomial

/-- Normal form of a real polynomial of total degree at most two in two variables. -/
theorem quad_normal_form (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) :
    ∃ a b c d e f : ℝ, ∀ z : Fin 2 → ℝ,
      eval z P = a + b * z 0 + c * z 1 + d * z 0 ^ 2 + e * z 0 * z 1 + f * z 1 ^ 2 := by
  classical
  refine ⟨∑ m ∈ P.support, if m 0 = 0 ∧ m 1 = 0 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 1 ∧ m 1 = 0 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 0 ∧ m 1 = 1 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 2 ∧ m 1 = 0 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 1 ∧ m 1 = 1 then P.coeff m else 0,
    ∑ m ∈ P.support, if m 0 = 0 ∧ m 1 = 2 then P.coeff m else 0, ?_⟩
  intro z
  rw [MvPolynomial.eval_eq']
  simp only [Fin.prod_univ_two]
  have key : ∀ m ∈ P.support, P.coeff m * (z 0 ^ m 0 * z 1 ^ m 1) =
      (if m 0 = 0 ∧ m 1 = 0 then P.coeff m else 0) +
      (if m 0 = 1 ∧ m 1 = 0 then P.coeff m else 0) * z 0 +
      (if m 0 = 0 ∧ m 1 = 1 then P.coeff m else 0) * z 1 +
      (if m 0 = 2 ∧ m 1 = 0 then P.coeff m else 0) * z 0 ^ 2 +
      (if m 0 = 1 ∧ m 1 = 1 then P.coeff m else 0) * z 0 * z 1 +
      (if m 0 = 0 ∧ m 1 = 2 then P.coeff m else 0) * z 1 ^ 2 := by
    intro m hm
    have hdeg := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hdeg
    have hs : m 0 + m 1 ≤ 2 := hdeg.trans hP
    have h0 : m 0 ≤ 2 := by omega
    have h1 : m 1 ≤ 2 := by omega
    interval_cases h : m 0 <;> interval_cases h' : m 1 <;> simp_all
    all_goals ring
  rw [Finset.sum_congr rfl key]
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

/-- One-variable Lagrange extrapolation of a quadratic from `0, 1/2, 1` to `[-4,5]`. -/
theorem quad_1d_extrap {α β γ B : ℝ} (h0 : |α| ≤ B)
    (hh : |α + β * (1 / 2) + γ * (1 / 2) ^ 2| ≤ B) (h1 : |α + β * 1 + γ * 1 ^ 2| ≤ B) :
    ∀ x : ℝ, x ∈ Set.Icc (-4 : ℝ) 5 → |α + β * x + γ * x ^ 2| ≤ 200 * B := by
  intro x hx
  obtain ⟨hxl, hxu⟩ := hx
  have hB : 0 ≤ B := (abs_nonneg _).trans h0
  set ph := α + β * (1 / 2) + γ * (1 / 2) ^ 2 with hph
  set p1 := α + β * 1 + γ * 1 ^ 2 with hp1
  have hid : α + β * x + γ * x ^ 2 =
      α * (2 * (x - 1 / 2) * (x - 1)) + ph * (-4 * x * (x - 1)) + p1 * (2 * x * (x - 1 / 2)) := by
    rw [hph, hp1]; ring
  have hL0 : |2 * (x - 1 / 2) * (x - 1)| ≤ 45 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x + 4) (by linarith : (0:ℝ) ≤ 5 - x)]
  have hL1 : |-4 * x * (x - 1)| ≤ 80 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x + 4) (by linarith : (0:ℝ) ≤ 5 - x)]
  have hL2 : |2 * x * (x - 1 / 2)| ≤ 45 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x + 4) (by linarith : (0:ℝ) ≤ 5 - x)]
  rw [hid]
  calc |α * (2 * (x - 1 / 2) * (x - 1)) + ph * (-4 * x * (x - 1)) + p1 * (2 * x * (x - 1 / 2))|
      ≤ |α * (2 * (x - 1 / 2) * (x - 1))| + |ph * (-4 * x * (x - 1))| +
          |p1 * (2 * x * (x - 1 / 2))| := abs_add_three _ _ _
    _ = |α| * |2 * (x - 1 / 2) * (x - 1)| + |ph| * |-4 * x * (x - 1)| +
          |p1| * |2 * x * (x - 1 / 2)| := by rw [abs_mul α, abs_mul ph, abs_mul p1]
    _ ≤ B * 45 + B * 80 + B * 45 := by
        gcongr
    _ ≤ 200 * B := by linarith

theorem vec_mem_Icc_unit {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (![x, y] : Fin 2 → ℝ) ∈ Set.Icc (0 : Fin 2 → ℝ) 1 := by
  constructor
  · intro i; fin_cases i
    · exact hx.1
    · exact hy.1
  · intro i; fin_cases i
    · exact hx.2
    · exact hy.2

/-- Remez on the unit square for total degree at most two. -/
theorem quad_remez (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (S : Set (Fin 2 → ℝ)) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : Fin 2 → ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ z ∈ S, |eval z P| ≤ E) :
    ∀ z ∈ Set.Icc (0 : Fin 2 → ℝ) 1, |eval z P| ≤ (48 / η) ^ 4 * E := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ := quad_normal_form P hP
  have hrow : ∀ x : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ 2 ∧
      ∀ y, p.eval y = eval ![x, y] P := by
    intro x
    refine ⟨Polynomial.C f * Polynomial.X ^ 2 + Polynomial.C (c + e * x) * Polynomial.X +
      Polynomial.C (a + b * x + d * x ^ 2), Polynomial.natDegree_quadratic_le, ?_⟩
    intro y
    rw [hnf]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hcol : ∀ y : ℝ, ∃ p : Polynomial ℝ, p.natDegree ≤ 2 ∧
      ∀ x, p.eval x = eval ![x, y] P := by
    intro y
    refine ⟨Polynomial.C d * Polynomial.X ^ 2 + Polynomial.C (b + e * y) * Polynomial.X +
      Polynomial.C (a + c * y + f * y ^ 2), Polynomial.natDegree_quadratic_le, ?_⟩
    intro x
    rw [hnf]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have h := Submission.Lib.K4PolynomialRemez.separately_polynomial_remez_box
    (fun z => eval z P) (MvPolynomial.continuous_eval P) 2 hrow hcol S hη hη1 hE hS hmass hbound
  intro z hz
  have hz' := h z hz
  have hfac : (16 * (((2 : ℕ) : ℝ) + 1) / η) ^ (2 * 2) = (48 / η) ^ 4 := by
    norm_num
  simpa only [hfac] using hz'

/-- Extrapolation of a quadratic from the unit square to `[-4,5]²`. -/
theorem quad_extrapolate (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {B : ℝ}
    (hB : ∀ z ∈ Set.Icc (0 : Fin 2 → ℝ) 1, |eval z P| ≤ B) :
    ∀ z : Fin 2 → ℝ, (∀ i, z i ∈ Set.Icc (-4 : ℝ) 5) → |eval z P| ≤ 10 ^ 6 * B := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ := quad_normal_form P hP
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hF : ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
      |(a + c * y + f * y ^ 2) + (b + e * y) * x + d * x ^ 2| ≤ B := by
    intro x y hx hy
    have h := hB _ (vec_mem_Icc_unit hx hy)
    rw [hnf] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    convert h using 2
    ring
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmemh : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- rows
  have hrow : ∀ x y : ℝ, x ∈ Set.Icc (-4 : ℝ) 5 → y ∈ Set.Icc (0 : ℝ) 1 →
      |(a + c * y + f * y ^ 2) + (b + e * y) * x + d * x ^ 2| ≤ 200 * B := by
    intro x y hx hy
    have h0 := hF 0 y hmem0 hy
    have hh := hF (1 / 2) y hmemh hy
    have h1 := hF 1 y hmem1 hy
    simp only [mul_zero, add_zero, zero_pow two_ne_zero] at h0
    exact quad_1d_extrap h0 hh h1 x hx
  -- columns
  have hcol : ∀ x y : ℝ, x ∈ Set.Icc (-4 : ℝ) 5 → y ∈ Set.Icc (-4 : ℝ) 5 →
      |(a + b * x + d * x ^ 2) + (c + e * x) * y + f * y ^ 2| ≤ 200 * (200 * B) := by
    intro x y hx hy
    have hrw : ∀ y', (a + b * x + d * x ^ 2) + (c + e * x) * y' + f * y' ^ 2 =
        (a + c * y' + f * y' ^ 2) + (b + e * y') * x + d * x ^ 2 := fun y' => by ring
    have h0 := hrow x 0 hx hmem0
    have hh := hrow x (1 / 2) hx hmemh
    have h1 := hrow x 1 hx hmem1
    rw [← hrw] at h0 hh h1
    simp only [mul_zero, add_zero, zero_pow two_ne_zero] at h0
    exact quad_1d_extrap h0 hh h1 y hy
  intro z hz
  have h := hcol (z 0) (z 1) (hz 0) (hz 1)
  rw [hnf]
  calc |a + b * z 0 + c * z 1 + d * z 0 ^ 2 + e * z 0 * z 1 + f * z 1 ^ 2|
      = |(a + b * z 0 + d * z 0 ^ 2) + (c + e * z 0) * z 1 + f * z 1 ^ 2| := by ring_nf
    _ ≤ 200 * (200 * B) := h
    _ ≤ 10 ^ 6 * B := by nlinarith

/-- Six interpolation points inside the disc of radius `1/2`. -/
noncomputable def sixPts : Fin 6 → Fin 2 → ℝ :=
  ![![0, 0], ![1 / 4, 0], ![-1 / 4, 0], ![0, 1 / 4], ![0, -1 / 4], ![1 / 4, 1 / 4]]

theorem sixPts_mem_disc (j : Fin 6) : sixPts j 0 ^ 2 + sixPts j 1 ^ 2 ≤ 1 / 4 := by
  fin_cases j <;> simp [sixPts] <;> norm_num

/-- Values at the six points control a quadratic on the square of half-width `1/4`. -/
theorem quad_six_points (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) {h : ℝ}
    (hpts : ∀ j : Fin 6, |eval (sixPts j) P| ≤ h) :
    ∀ z : Fin 2 → ℝ, (∀ i, |z i| ≤ 1 / 4) → |eval z P| ≤ 100 * h := by
  obtain ⟨a, b, c, d, e, f, hnf⟩ := quad_normal_form P hP
  have q0 := hpts 0
  have q1 := hpts 1
  have q2 := hpts 2
  have q3 := hpts 3
  have q4 := hpts 4
  have q5 := hpts 5
  simp only [hnf, sixPts] at q0 q1 q2 q3 q4 q5
  norm_num at q0 q1 q2 q3 q4 q5
  have hh0 : 0 ≤ h := (abs_nonneg _).trans q0
  rw [abs_le] at q0 q1 q2 q3 q4 q5
  have ha : |a| ≤ h := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |b| ≤ 4 * h := abs_le.mpr ⟨by linarith, by linarith⟩
  have hc : |c| ≤ 4 * h := abs_le.mpr ⟨by linarith, by linarith⟩
  have hd : |d| ≤ 32 * h := abs_le.mpr ⟨by linarith, by linarith⟩
  have hf : |f| ≤ 32 * h := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : |e| ≤ 128 * h := abs_le.mpr ⟨by linarith, by linarith⟩
  intro z hz
  have hz0 := hz 0
  have hz1 := hz 1
  rw [hnf]
  have t1 : |b * z 0| ≤ 4 * h * (1 / 4) := by
    rw [abs_mul]; exact mul_le_mul hb hz0 (abs_nonneg _) (by linarith)
  have t2 : |c * z 1| ≤ 4 * h * (1 / 4) := by
    rw [abs_mul]; exact mul_le_mul hc hz1 (abs_nonneg _) (by linarith)
  have hz0sq : |z 0 ^ 2| ≤ 1 / 16 := by
    rw [abs_pow]; nlinarith [abs_nonneg (z 0)]
  have hz1sq : |z 1 ^ 2| ≤ 1 / 16 := by
    rw [abs_pow]; nlinarith [abs_nonneg (z 1)]
  have hz01 : |z 0 * z 1| ≤ 1 / 16 := by
    rw [abs_mul]; nlinarith [abs_nonneg (z 0), abs_nonneg (z 1)]
  have t3 : |d * z 0 ^ 2| ≤ 32 * h * (1 / 16) := by
    rw [abs_mul]; exact mul_le_mul hd hz0sq (abs_nonneg _) (by linarith)
  have t4 : |e * z 0 * z 1| ≤ 128 * h * (1 / 16) := by
    rw [mul_assoc, abs_mul]; exact mul_le_mul he hz01 (abs_nonneg _) (by linarith)
  have t5 : |f * z 1 ^ 2| ≤ 32 * h * (1 / 16) := by
    rw [abs_mul]; exact mul_le_mul hf hz1sq (abs_nonneg _) (by linarith)
  calc |a + b * z 0 + c * z 1 + d * z 0 ^ 2 + e * z 0 * z 1 + f * z 1 ^ 2|
      ≤ |a| + |b * z 0| + |c * z 1| + |d * z 0 ^ 2| + |e * z 0 * z 1| + |f * z 1 ^ 2| := by
        have := abs_add_le (a + b * z 0 + c * z 1 + d * z 0 ^ 2 + e * z 0 * z 1) (f * z 1 ^ 2)
        have := abs_add_le (a + b * z 0 + c * z 1 + d * z 0 ^ 2) (e * z 0 * z 1)
        have := abs_add_le (a + b * z 0 + c * z 1) (d * z 0 ^ 2)
        have := abs_add_le (a + b * z 0) (c * z 1)
        have := abs_add_le a (b * z 0)
        linarith
    _ ≤ 100 * h := by linarith

end Submission.Obl.k4_scalar_candidate_original_return.QuadBounds
