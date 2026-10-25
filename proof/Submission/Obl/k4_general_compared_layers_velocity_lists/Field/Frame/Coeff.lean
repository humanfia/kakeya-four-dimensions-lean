-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Coeff; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Point

/-!
# Scalar coefficients of a line in the normalized block

In the normalized time `u` of a block `Q`, the major coordinate of a line is the affine
`scalarY` with coefficients `((Z(t₀) - c₀ - c₁ t₀) / q, b₃ - c₁)`, and the native residual
`P(x) - background(base)` is a quadratic in `u` (an affine substitution in polynomials of
total degree at most two); its coefficients are read off its values at `0, 1/2, 1`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent.FieldFrame

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The native residual of a line against the background, in normalized block time. -/
def resid (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (Cf : Fin 4 → ℝ) (l : α) (u : ℝ) : ℝ :=
  p.signal k l (p.blockStart k r Q + p.blockLen k r * u) -
    eval (p.base k l (p.blockStart k r Q + p.blockLen k r * u))
      (bgPoly (p.blockStart k r Q) (p.blockLen k r) (p.blockWidth k r) (p.c k r Q) Cf)

/-- The scalar coefficients of a line in the normalized block. -/
def rawCoeff (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (Cf : Fin 4 → ℝ) (l : α) : Fin 5 → ℝ :=
  ![(p.x k l (p.blockStart k r Q) 1 - p.c k r Q 0 - p.c k r Q 1 * p.blockStart k r Q) /
      p.blockLen k r,
    p.b k l 3 - p.c k r Q 1,
    resid p k r Q Cf l 0,
    4 * resid p k r Q Cf l (1 / 2) - resid p k r Q Cf l 1 - 3 * resid p k r Q Cf l 0,
    2 * resid p k r Q Cf l 1 - 4 * resid p k r Q Cf l (1 / 2) + 2 * resid p k r Q Cf l 0]

theorem x_affine (k : ℕ) (l : α) (t₀ q u : ℝ) :
    p.x k l (t₀ + q * u) =
      fun i => p.x k l t₀ i + u * (q * (![1, p.b k l 3, p.b k l 4, p.b k l 5] : Fin 4 → ℝ) i) := by
  funext i
  fin_cases i <;>
    simp [Submission.Obl.k4_critical_intercept_concentration.Data.x] <;> ring

theorem base_affine (k : ℕ) (l : α) (t₀ q u : ℝ) :
    p.base k l (t₀ + q * u) =
      fun i => p.base k l t₀ i + u * (q * (![1, p.b k l 3, p.b k l 4] : Fin 3 → ℝ) i) := by
  funext i
  fin_cases i <;>
    simp [Parent.base, Submission.Obl.k4_critical_intercept_concentration.Data.x] <;> ring

theorem resid_quadratic {k : ℕ} (hP : (p.P k).totalDegree ≤ 2) (r : ℝ) (Q : Fin (p.n k r))
    (Cf : Fin 4 → ℝ) (l : α) :
    ∃ c : Fin 3 → ℝ, ∀ u, resid p k r Q Cf l u = c 0 + c 1 * u + c 2 * u ^ 2 := by
  obtain ⟨c₁, hc₁⟩ := affine_eval_quadratic (p.P k) hP (p.x k l (p.blockStart k r Q))
    (fun i => p.blockLen k r * (![1, p.b k l 3, p.b k l 4, p.b k l 5] : Fin 4 → ℝ) i)
  obtain ⟨c₂, hc₂⟩ := affine_eval_quadratic
    (bgPoly (p.blockStart k r Q) (p.blockLen k r) (p.blockWidth k r) (p.c k r Q) Cf)
    (totalDegree_bgPoly _ _ _ _ _) (p.base k l (p.blockStart k r Q))
    (fun i => p.blockLen k r * (![1, p.b k l 3, p.b k l 4] : Fin 3 → ℝ) i)
  refine ⟨fun i => c₁ i - c₂ i, fun u => ?_⟩
  unfold resid Parent.signal
  rw [x_affine, base_affine, hc₁ u, hc₂ u]
  ring

theorem scalarX_rawCoeff {k : ℕ} (hP : (p.P k).totalDegree ≤ 2) (r : ℝ) (Q : Fin (p.n k r))
    (Cf : Fin 4 → ℝ) (l : α) (u : ℝ) :
    scalarX (rawCoeff p k r Q Cf l) u = resid p k r Q Cf l u := by
  obtain ⟨c, hc⟩ := resid_quadratic p hP r Q Cf l
  have h := quadratic_interp (f := resid p k r Q Cf l) hc u
  simp only [scalarX, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarX, rawCoeff,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_three,
    Matrix.cons_val_four]
  rw [← h]

theorem scalarY_rawCoeff (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) (Cf : Fin 4 → ℝ) (l : α)
    (u : ℝ) :
    scalarY (rawCoeff p k r Q Cf l) u =
      (p.x k l (p.blockStart k r Q + p.blockLen k r * u) 1 - p.c k r Q 0 -
        p.c k r Q 1 * (p.blockStart k r Q + p.blockLen k r * u)) / p.blockLen k r := by
  have hq : p.blockLen k r ≠ 0 := (blockLen_pos p k r).ne'
  simp only [scalarY, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY, rawCoeff,
    Matrix.cons_val_zero, Matrix.cons_val_one, x_one]
  field_simp
  ring

theorem measurable_x_line {k : ℕ} (hb : Measurable (p.b k)) (t : ℝ) :
    Measurable (fun l => p.x k l t) := by
  unfold Submission.Obl.k4_critical_intercept_concentration.Data.x
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i <;> simp <;> fun_prop

theorem measurable_resid {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r))
    (Cf : Fin 4 → ℝ) (u : ℝ) : Measurable (fun l => resid p k r Q Cf l u) := by
  unfold resid Parent.signal Parent.base
  have hx := measurable_x_line p hb (p.blockStart k r Q + p.blockLen k r * u)
  refine Measurable.sub ((MvPolynomial.continuous_eval (p.P k)).measurable.comp hx) ?_
  refine (MvPolynomial.continuous_eval _).measurable.comp ?_
  exact measurable_pi_iff.mpr fun i => (measurable_pi_iff.mp hx) (Fin.castSucc i)

theorem measurable_rawCoeff {k : ℕ} (hb : Measurable (p.b k)) (r : ℝ) (Q : Fin (p.n k r))
    (Cf : Fin 4 → ℝ) : Measurable (rawCoeff p k r Q Cf) := by
  have h0 := measurable_resid p hb r Q Cf 0
  have h1 := measurable_resid p hb r Q Cf 1
  have h2 := measurable_resid p hb r Q Cf (1 / 2)
  have hx := measurable_pi_iff.mp (measurable_x_line p hb (p.blockStart k r Q)) 1
  have hb3 : Measurable (fun l => p.b k l 3) := measurable_pi_iff.mp hb 3
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact ((hx.sub_const _).sub_const _).div_const _
  · exact hb3.sub_const _
  · exact h0
  · exact ((h2.const_mul _).sub h1).sub (h0.const_mul _)
  · exact ((h1.const_mul _).sub (h2.const_mul _)).add (h0.const_mul _)

/-- The bound of the background on an incidence of the block. -/
theorem abs_eval_bgPoly_le {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {Cf : Fin 4 → ℝ} {B : ℝ}
    (hK1 : 1 ≤ p.K k) (hB : ∀ i, |Cf i| ≤ B) {l : α} {t : ℝ}
    (ht : t ∈ block (p.T k r) (p.j k r Q))
    (hζ : |p.x k l t 1 - p.c k r Q 0 - t * p.c k r Q 1| ≤ p.K k * p.blockLen k r)
    (hU : |p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1| ≤
      p.K k * p.blockWidth k r) (hN : 0 < p.N k) :
    |eval (p.base k l t)
        (bgPoly (p.blockStart k r Q) (p.blockLen k r) (p.blockWidth k r) (p.c k r Q) Cf)| ≤
      4 * p.K k ^ 2 * B := by
  have hq0 : 0 < p.blockLen k r := blockLen_pos p k r
  have hw0 : 0 < p.blockWidth k r := by
    unfold Parent.blockWidth
    exact mul_pos hq0 (Real.rpow_pos_of_pos hN _)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [block_eq_Icc] at ht
  rw [base_eq, eval_bgPoly]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  set K := p.K k
  have hτ : |(t - p.blockStart k r Q) / p.blockLen k r| ≤ 1 := by
    rw [abs_div, abs_of_pos hq0, div_le_one hq0, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hζ' : |(p.x k l t 1 - p.c k r Q 0 - p.c k r Q 1 * t) / p.blockLen k r| ≤ K := by
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    have heq : p.x k l t 1 - p.c k r Q 0 - p.c k r Q 1 * t =
        p.x k l t 1 - p.c k r Q 0 - t * p.c k r Q 1 := by ring
    rw [heq]
    exact hζ
  have hU' : |(p.x k l t 2 - p.c k r Q 2 - p.c k r Q 3 * t - p.c k r Q 4 * p.x k l t 1) /
      p.blockWidth k r| ≤ K := by
    rw [abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    have heq : p.x k l t 2 - p.c k r Q 2 - p.c k r Q 3 * t - p.c k r Q 4 * p.x k l t 1 =
        p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1 := by ring
    rw [heq]
    exact hU
  set τ := (t - p.blockStart k r Q) / p.blockLen k r
  set ζ := (p.x k l t 1 - p.c k r Q 0 - p.c k r Q 1 * t) / p.blockLen k r
  set U := (p.x k l t 2 - p.c k r Q 2 - p.c k r Q 3 * t - p.c k r Q 4 * p.x k l t 1) /
    p.blockWidth k r
  have hK0 : 0 ≤ K := by linarith
  have hC1 : |Cf 0 + Cf 1 * τ + Cf 2 * ζ| ≤ 3 * K * B := by
    have e1 : |Cf 1 * τ| ≤ B * 1 := by
      rw [abs_mul]; exact mul_le_mul (hB 1) hτ (abs_nonneg _) hB0
    have e2 : |Cf 2 * ζ| ≤ B * K := by
      rw [abs_mul]; exact mul_le_mul (hB 2) hζ' (abs_nonneg _) hB0
    have e3 : |Cf 0 + Cf 1 * τ + Cf 2 * ζ| ≤ |Cf 0| + |Cf 1 * τ| + |Cf 2 * ζ| := by
      refine (abs_add_le _ _).trans ?_
      gcongr
      exact abs_add_le _ _
    have e4 : B ≤ K * B := le_mul_of_one_le_left hB0 hK1
    have e5 := hB 0
    nlinarith
  have hU2 : |U ^ 2| ≤ K ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hU' 2
  have hKK : K ≤ K ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left hK0 hK1
  calc |(Cf 0 + Cf 1 * τ + Cf 2 * ζ) * U + Cf 3 * U ^ 2|
      ≤ |(Cf 0 + Cf 1 * τ + Cf 2 * ζ) * U| + |Cf 3 * U ^ 2| := abs_add_le _ _
    _ ≤ (3 * K * B) * K + B * K ^ 2 := by
        rw [abs_mul, abs_mul]
        gcongr
        exact hB 3
    _ = 4 * K ^ 2 * B := by ring

/-- The scalar coefficients of a line of the block with bounded native signal. -/
theorem abs_rawCoeff_le {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {Cf : Fin 4 → ℝ} {B : ℝ}
    (hK1 : 1 ≤ p.K k) (hB : ∀ i, |Cf i| ≤ B) (hB1 : 1 ≤ B) (hN : 0 < p.N k) {l : α}
    (hc : ∀ e, |p.c k r Q e| ≤ p.K k) (hb3 : |p.b k l 3| ≤ p.K k)
    (hgeo : ∀ t ∈ block (p.T k r) (p.j k r Q),
      |p.x k l t 1 - p.c k r Q 0 - t * p.c k r Q 1| ≤ p.K k * p.blockLen k r ∧
      |p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1| ≤
        p.K k * p.blockWidth k r)
    (hsig : ∀ t ∈ block (p.T k r) (p.j k r Q), |p.signal k l t| ≤ p.K k) :
    ∀ i, |rawCoeff p k r Q Cf l i| ≤ 40 * p.K k ^ 2 * B := by
  have hq0 : 0 < p.blockLen k r := blockLen_pos p k r
  set K := p.K k with hK_def
  have hK0 : 0 ≤ K := by linarith
  have hKK : K ≤ K ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left hK0 hK1
  have hKB : K ^ 2 ≤ K ^ 2 * B := le_mul_of_one_le_right (by positivity) hB1
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1,
      p.blockStart k r Q + p.blockLen k r * u ∈ block (p.T k r) (p.j k r Q) := by
    intro u hu
    rw [block_eq_Icc]
    constructor
    · nlinarith [hu.1]
    · nlinarith [hu.2]
  have hres : ∀ u ∈ Icc (0 : ℝ) 1, |resid p k r Q Cf l u| ≤ 5 * K ^ 2 * B := by
    intro u hu
    have ht := hmem u hu
    obtain ⟨hζ, hU⟩ := hgeo _ ht
    have h1 := hsig _ ht
    have h2 := abs_eval_bgPoly_le p hK1 hB ht hζ hU hN
    unfold resid
    calc _ ≤ |p.signal k l (p.blockStart k r Q + p.blockLen k r * u)| +
          |eval (p.base k l (p.blockStart k r Q + p.blockLen k r * u))
            (bgPoly (p.blockStart k r Q) (p.blockLen k r) (p.blockWidth k r) (p.c k r Q) Cf)| :=
          abs_sub _ _
      _ ≤ K + 4 * K ^ 2 * B := add_le_add h1 h2
      _ ≤ 5 * K ^ 2 * B := by nlinarith
  have r0 := hres 0 ⟨le_rfl, zero_le_one⟩
  have r1 := hres 1 ⟨zero_le_one, le_rfl⟩
  have r2 := hres (1 / 2) ⟨by norm_num, by norm_num⟩
  have hR0 : 0 ≤ 5 * K ^ 2 * B := by positivity
  intro i
  fin_cases i
  · simp only [rawCoeff, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    have ht₀ : p.blockStart k r Q ∈ block (p.T k r) (p.j k r Q) := by
      rw [block_eq_Icc]
      exact ⟨le_rfl, by linarith⟩
    obtain ⟨hζ, -⟩ := hgeo _ ht₀
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    have heq : p.x k l (p.blockStart k r Q) 1 - p.c k r Q 0 - p.c k r Q 1 * p.blockStart k r Q =
        p.x k l (p.blockStart k r Q) 1 - p.c k r Q 0 - p.blockStart k r Q * p.c k r Q 1 := by
      ring
    rw [heq]
    refine hζ.trans (mul_le_mul_of_nonneg_right ?_ hq0.le)
    nlinarith
  · simp only [rawCoeff, Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
    calc |p.b k l 3 - p.c k r Q 1| ≤ |p.b k l 3| + |p.c k r Q 1| := abs_sub _ _
      _ ≤ K + K := add_le_add hb3 (hc 1)
      _ ≤ 40 * K ^ 2 * B := by nlinarith
  · simp only [rawCoeff, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    nlinarith
  · simp only [rawCoeff, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons]
    calc _ ≤ |4 * resid p k r Q Cf l (1 / 2)| + |resid p k r Q Cf l 1| +
          |3 * resid p k r Q Cf l 0| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ 4 * (5 * K ^ 2 * B) + 5 * K ^ 2 * B + 3 * (5 * K ^ 2 * B) := by
          rw [abs_mul, abs_mul]
          norm_num
          gcongr
      _ ≤ 40 * K ^ 2 * B := by nlinarith
  · simp only [rawCoeff, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_four, Matrix.tail_cons,
      Matrix.head_cons]
    calc _ ≤ |2 * resid p k r Q Cf l 1| + |4 * resid p k r Q Cf l (1 / 2)| +
          |2 * resid p k r Q Cf l 0| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ 2 * (5 * K ^ 2 * B) + 4 * (5 * K ^ 2 * B) + 2 * (5 * K ^ 2 * B) := by
          rw [abs_mul, abs_mul, abs_mul]
          norm_num
          gcongr
      _ ≤ 40 * K ^ 2 * B := by nlinarith

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
