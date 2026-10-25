import Mathlib
import Submission.Lib.K4ContactNormalization
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Zooming into a parent box

A true parent label at depth `r` has a time block `[t₀, t₀ + q]`, a major
coordinate `x₁` close to a constant `z₀` at the start of the block, a tilted
transverse coordinate `x₂ - c₂ - c₃ t - c₄ x₁` of width `w = q g`, and a hidden
coordinate fitted at width `a`. The zoom is the affine change of variables

`t' = (t - t₀)/q`, `x₁' = (x₁ - z₀)/q`, `x₂' = (x₂ - c₂ - c₃ t - c₄ x₁)/w`,
`x₃' = (x₃ - h₀)/a`.

It maps trajectories to trajectories (`coeff`), keeps the major velocity `b₃`
(so the velocity palette is unchanged), and polynomials are transported in
both directions (`lift`, `push`) with exact control of the hidden derivatives:
a fit at width `c` in zoomed coordinates is a fit at width `a * c` in the
original ones, with the same hidden-derivative budget.
-/

namespace Submission.Lib.K4ContactTransfer

open MvPolynomial
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4ContactNormalization (point)

noncomputable section

/-- Affine data of a parent zoom. -/
structure Zoom where
  /-- start of the time block -/
  t₀ : ℝ
  /-- length of the time block -/
  q : ℝ
  /-- major coordinate at the start of the block -/
  z₀ : ℝ
  /-- transverse intercept of the tilted box -/
  c₂ : ℝ
  /-- transverse time slope of the tilted box -/
  c₃ : ℝ
  /-- transverse skew of the tilted box -/
  c₄ : ℝ
  /-- transverse width -/
  w : ℝ
  /-- hidden centre -/
  h₀ : ℝ
  /-- hidden width -/
  a : ℝ

namespace Zoom

variable (Z : Zoom)

/-- Zoomed time. -/
def time (t : ℝ) : ℝ := (t - Z.t₀) / Z.q

/-- Original time of a zoomed time. -/
def untime (t : ℝ) : ℝ := Z.t₀ + Z.q * t

/-- Zoomed position of a point `(t, x₁, x₂, x₃)`. -/
def pos (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(x 0 - Z.t₀) / Z.q, (x 1 - Z.z₀) / Z.q,
    (x 2 - Z.c₂ - Z.c₃ * x 0 - Z.c₄ * x 1) / Z.w, (x 3 - Z.h₀) / Z.a]

/-- Original position of a zoomed point. -/
def unpos (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![Z.t₀ + Z.q * y 0, Z.z₀ + Z.q * y 1,
    Z.c₂ + Z.c₃ * (Z.t₀ + Z.q * y 0) + Z.c₄ * (Z.z₀ + Z.q * y 1) + Z.w * y 2,
    Z.h₀ + Z.a * y 3]

/-- Zoomed trajectory coefficients. -/
def coeff (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(b 0 + Z.t₀ * b 3 - Z.z₀) / Z.q,
    ((b 1 - Z.c₂ - Z.c₄ * b 0) + Z.t₀ * (b 4 - Z.c₃ - Z.c₄ * b 3)) / Z.w,
    (b 2 + Z.t₀ * b 5 - Z.h₀) / Z.a,
    b 3,
    Z.q * (b 4 - Z.c₃ - Z.c₄ * b 3) / Z.w,
    Z.q * b 5 / Z.a]

/-- Nondegeneracy of a zoom. -/
structure Ok : Prop where
  q_ne : Z.q ≠ 0
  w_ne : Z.w ≠ 0
  a_ne : Z.a ≠ 0

variable {Z}

theorem untime_time (hZ : Z.Ok) (t : ℝ) : Z.untime (Z.time t) = t := by
  have := hZ.q_ne
  simp only [untime, time]
  field_simp
  ring

theorem time_untime (hZ : Z.Ok) (t : ℝ) : Z.time (Z.untime t) = t := by
  have := hZ.q_ne
  simp only [untime, time]
  field_simp
  ring

theorem unpos_pos (hZ : Z.Ok) (x : Fin 4 → ℝ) : Z.unpos (Z.pos x) = x := by
  have := hZ.q_ne
  have := hZ.w_ne
  have := hZ.a_ne
  funext i
  fin_cases i <;> simp [unpos, pos] <;> field_simp <;> ring

theorem pos_unpos (hZ : Z.Ok) (y : Fin 4 → ℝ) : Z.pos (Z.unpos y) = y := by
  have := hZ.q_ne
  have := hZ.w_ne
  have := hZ.a_ne
  funext i
  fin_cases i <;> simp [unpos, pos] <;> field_simp <;> ring

/-- The zoom maps trajectory points to trajectory points. -/
theorem pos_point (hZ : Z.Ok) (b : Fin 6 → ℝ) (t : ℝ) :
    Z.pos (point b t) = point (Z.coeff b) (Z.time t) := by
  have := hZ.q_ne
  have := hZ.w_ne
  have := hZ.a_ne
  funext i
  fin_cases i <;> simp [pos, point, coeff, time] <;> field_simp <;> ring

theorem point_untime (hZ : Z.Ok) (b : Fin 6 → ℝ) (t : ℝ) :
    point (Z.coeff b) t = Z.pos (point b (Z.untime t)) := by
  rw [pos_point hZ, time_untime hZ]

/-- The major velocity is kept. -/
theorem coeff_three (b : Fin 6 → ℝ) : Z.coeff b 3 = b 3 := rfl

/-- The zoomed transverse velocity is the normalized strip error. -/
theorem coeff_four (b : Fin 6 → ℝ) :
    Z.coeff b 4 = Z.q * (b 4 - Z.c₃ - Z.c₄ * b 3) / Z.w := rfl

theorem coeff_zero (b : Fin 6 → ℝ) :
    Z.coeff b 0 = (b 0 + Z.t₀ * b 3 - Z.z₀) / Z.q := rfl

theorem coeff_one (b : Fin 6 → ℝ) :
    Z.coeff b 1 = ((b 1 - Z.c₂ - Z.c₄ * b 0) + Z.t₀ * (b 4 - Z.c₃ - Z.c₄ * b 3)) / Z.w :=
  rfl

theorem measurable_coeff : Measurable Z.coeff := by
  unfold coeff
  fun_prop

/-! ## Polynomial transport -/

variable (Z)

/-- Zoomed coordinates as degree-one polynomials in the original ones. -/
def subst : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C Z.q⁻¹ * (X 0 - C Z.t₀), C Z.q⁻¹ * (X 1 - C Z.z₀),
    C Z.w⁻¹ * (X 2 - C Z.c₂ - C Z.c₃ * X 0 - C Z.c₄ * X 1),
    C Z.a⁻¹ * (X 3 - C Z.h₀)]

/-- Original coordinates as degree-one polynomials in the zoomed ones. -/
def unsubst : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C Z.t₀ + C Z.q * X 0, C Z.z₀ + C Z.q * X 1,
    C Z.c₂ + C Z.c₃ * (C Z.t₀ + C Z.q * X 0) + C Z.c₄ * (C Z.z₀ + C Z.q * X 1) +
      C Z.w * X 2,
    C Z.h₀ + C Z.a * X 3]

/-- A zoomed test, read in the original coordinates and scaled back to the
original hidden width. -/
def lift (Q : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  C Z.a * bind₁ Z.subst Q

/-- An original test, read in the zoomed coordinates and divided by the hidden
width. -/
def push (F : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  C Z.a⁻¹ * bind₁ Z.unsubst F

variable {Z}

theorem eval_subst (x : Fin 4 → ℝ) : (fun i => eval x (Z.subst i)) = Z.pos x := by
  funext i
  fin_cases i <;> simp [subst, pos, div_eq_mul_inv] <;> ring

theorem eval_unsubst (y : Fin 4 → ℝ) : (fun i => eval y (Z.unsubst i)) = Z.unpos y := by
  funext i
  fin_cases i <;> simp [unsubst, unpos]

theorem subst_degree (i : Fin 4) : (Z.subst i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_C_mul _ (deg1_sub (deg1_sub (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _)))
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))

theorem unsubst_degree (i : Fin 4) : (Z.unsubst i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_add (deg1_add (deg1_C _)
      (deg1_C_mul _ (deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _)))))
      (deg1_C_mul _ (deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _)))))
      (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))

theorem lift_degree (Q : MvPolynomial (Fin 4) ℝ) :
    (Z.lift Q).totalDegree ≤ Q.totalDegree := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact totalDegree_bind₁_le_of_le_one _ subst_degree Q

theorem push_degree (F : MvPolynomial (Fin 4) ℝ) :
    (Z.push F).totalDegree ≤ F.totalDegree := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact totalDegree_bind₁_le_of_le_one _ unsubst_degree F

theorem eval_lift (Q : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    eval x (Z.lift Q) = Z.a * eval (Z.pos x) Q := by
  rw [lift, eval_mul, eval_C, eval_bind₁', eval_subst]

theorem eval_push (F : MvPolynomial (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    eval y (Z.push F) = Z.a⁻¹ * eval (Z.unpos y) F := by
  rw [push, eval_mul, eval_C, eval_bind₁', eval_unsubst]

theorem pderiv_subst (i : Fin 4) :
    pderiv (3 : Fin 4) (Z.subst i) = if i = 3 then C Z.a⁻¹ else 0 := by
  fin_cases i <;> simp [subst, pderiv_X]

theorem pderiv_unsubst (i : Fin 4) :
    pderiv (3 : Fin 4) (Z.unsubst i) = if i = 3 then C Z.a else 0 := by
  fin_cases i <;> simp [unsubst, pderiv_X]

/-- Chain rule for a substitution whose only hidden dependence is through the
hidden coordinate, with constant factor `κ`. -/
theorem pderiv_bind₁_hidden (σ : Fin 4 → MvPolynomial (Fin 4) ℝ) (κ : ℝ)
    (hσ : ∀ i, pderiv (3 : Fin 4) (σ i) = if i = 3 then C κ else 0)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (bind₁ σ Q) = C κ * bind₁ σ (pderiv (3 : Fin 4) Q) := by
  rw [pderiv_bind₁]
  rw [Finset.sum_eq_single (3 : Fin 4)]
  · rw [hσ 3, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    ring
  · intro i _ hi
    rw [hσ i, ite_eq_right_iff.mpr (fun h => absurd h hi), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pderiv_lift (hZ : Z.Ok) (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (Z.lift Q) = bind₁ Z.subst (pderiv (3 : Fin 4) Q) := by
  rw [lift, Derivation.leibniz, pderiv_C, smul_zero, add_zero,
    pderiv_bind₁_hidden _ _ pderiv_subst, smul_eq_mul, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ hZ.a_ne, C_1, one_mul]

theorem pderiv_pderiv_lift (hZ : Z.Ok) (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (Z.lift Q)) =
      C Z.a⁻¹ * bind₁ Z.subst (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) := by
  rw [pderiv_lift hZ, pderiv_bind₁_hidden _ _ pderiv_subst]

theorem pderiv_push (hZ : Z.Ok) (F : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (Z.push F) = bind₁ Z.unsubst (pderiv (3 : Fin 4) F) := by
  rw [push, Derivation.leibniz, pderiv_C, smul_zero, add_zero,
    pderiv_bind₁_hidden _ _ pderiv_unsubst, smul_eq_mul, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ hZ.a_ne, C_1, one_mul]

theorem pderiv_pderiv_push (hZ : Z.Ok) (F : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (Z.push F)) =
      C Z.a * bind₁ Z.unsubst (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) F)) := by
  rw [pderiv_push hZ, pderiv_bind₁_hidden _ _ pderiv_unsubst]

theorem eval_pderiv_lift (hZ : Z.Ok) (Q : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    eval x (pderiv (3 : Fin 4) (Z.lift Q)) = eval (Z.pos x) (pderiv (3 : Fin 4) Q) := by
  rw [pderiv_lift hZ, eval_bind₁', eval_subst]

theorem eval_pderiv_pderiv_lift (hZ : Z.Ok) (Q : MvPolynomial (Fin 4) ℝ)
    (x : Fin 4 → ℝ) :
    eval x (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (Z.lift Q))) =
      Z.a⁻¹ * eval (Z.pos x) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) := by
  rw [pderiv_pderiv_lift hZ, eval_mul, eval_C, eval_bind₁', eval_subst]

theorem eval_pderiv_push (hZ : Z.Ok) (F : MvPolynomial (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    eval y (pderiv (3 : Fin 4) (Z.push F)) = eval (Z.unpos y) (pderiv (3 : Fin 4) F) := by
  rw [pderiv_push hZ, eval_bind₁', eval_unsubst]

theorem eval_pderiv_pderiv_push (hZ : Z.Ok) (F : MvPolynomial (Fin 4) ℝ)
    (y : Fin 4 → ℝ) :
    eval y (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (Z.push F))) =
      Z.a * eval (Z.unpos y) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) F)) := by
  rw [pderiv_pderiv_push hZ, eval_mul, eval_C, eval_bind₁', eval_unsubst]

/-- Push and lift are inverse to each other. -/
theorem lift_push (hZ : Z.Ok) (F : MvPolynomial (Fin 4) ℝ) : Z.lift (Z.push F) = F := by
  apply MvPolynomial.funext
  intro x
  rw [eval_lift, eval_push, unpos_pos hZ, ← mul_assoc, mul_inv_cancel₀ hZ.a_ne, one_mul]

theorem push_lift (hZ : Z.Ok) (Q : MvPolynomial (Fin 4) ℝ) : Z.push (Z.lift Q) = Q := by
  apply MvPolynomial.funext
  intro y
  rw [eval_push, eval_lift, pos_unpos hZ, ← mul_assoc, inv_mul_cancel₀ hZ.a_ne, one_mul]

/-! ## Fits along trajectories -/

/-- The three fit inequalities of a test along a trajectory on a time set. -/
def Fits (Q : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (I : Set ℝ) (H c : ℝ) : Prop :=
  ∀ t ∈ I, |eval (point b t) Q| ≤ H * c ∧
    |eval (point b t) (pderiv (3 : Fin 4) Q)| ≤ H ∧
    |eval (point b t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤ H / c

/-- A zoomed fit at width `c` lifts to an original fit at width `a * c` on the
corresponding original times. -/
theorem lift_fits (hZ : Z.Ok) (ha : 0 < Z.a) {Q : MvPolynomial (Fin 4) ℝ}
    {b : Fin 6 → ℝ} {I : Set ℝ} {H c : ℝ}
    (h : Fits Q (Z.coeff b) I H c) :
    Fits (Z.lift Q) b (Z.time ⁻¹' I) H (Z.a * c) := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := h (Z.time t) ht
  rw [eval_lift, eval_pderiv_lift hZ, eval_pderiv_pderiv_lift hZ, pos_point hZ]
  refine ⟨?_, hd, ?_⟩
  · rw [abs_mul, abs_of_pos ha]
    calc Z.a * |eval (point (Z.coeff b) (Z.time t)) Q| ≤ Z.a * (H * c) :=
          mul_le_mul_of_nonneg_left hv ha.le
      _ = H * (Z.a * c) := by ring
  · rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc Z.a⁻¹ * |eval (point (Z.coeff b) (Z.time t)) (pderiv 3 (pderiv 3 Q))|
        ≤ Z.a⁻¹ * (H / c) := mul_le_mul_of_nonneg_left hdd (inv_pos.mpr ha).le
      _ = H / (Z.a * c) := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

/-- An original fit at width `c` pushes to a zoomed fit at width `c / a`. -/
theorem push_fits (hZ : Z.Ok) (ha : 0 < Z.a) {F : MvPolynomial (Fin 4) ℝ}
    {b : Fin 6 → ℝ} {I : Set ℝ} {H c : ℝ}
    (h : Fits F b I H c) :
    Fits (Z.push F) (Z.coeff b) (Z.untime ⁻¹' I) H (c / Z.a) := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := h (Z.untime t) ht
  have hpt : Z.unpos (point (Z.coeff b) t) = point b (Z.untime t) := by
    rw [point_untime hZ, unpos_pos hZ]
  rw [eval_push, eval_pderiv_push hZ, eval_pderiv_pderiv_push hZ, hpt]
  refine ⟨?_, hd, ?_⟩
  · rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc Z.a⁻¹ * |eval (point b (Z.untime t)) F| ≤ Z.a⁻¹ * (H * c) :=
          mul_le_mul_of_nonneg_left hv (inv_pos.mpr ha).le
      _ = H * (c / Z.a) := by rw [div_eq_mul_inv]; ring
  · rw [abs_mul, abs_of_pos ha]
    have hc : H / (c / Z.a) = Z.a * (H / c) := by
      rw [div_div_eq_mul_div]; ring
    rw [hc]
    exact mul_le_mul_of_nonneg_left hdd ha.le

/-! ## Coefficient budgets -/

/-- An `ℓ¹` bound for the zoomed coordinates as original polynomials. -/
def liftBudget : ℝ :=
  1 + |Z.q⁻¹| * (1 + |Z.t₀| + |Z.z₀|) +
    |Z.w⁻¹| * (1 + |Z.c₂| + |Z.c₃| + |Z.c₄|) + |Z.a⁻¹| * (1 + |Z.h₀|)

theorem one_le_liftBudget : 1 ≤ Z.liftBudget := by
  have h1 : 0 ≤ |Z.q⁻¹| * (1 + |Z.t₀| + |Z.z₀|) := by positivity
  have h2 : 0 ≤ |Z.w⁻¹| * (1 + |Z.c₂| + |Z.c₃| + |Z.c₄|) := by positivity
  have h3 : 0 ≤ |Z.a⁻¹| * (1 + |Z.h₀|) := by positivity
  simp only [liftBudget]
  linarith

theorem coeffL1_C_mul_sub_C (u v : ℝ) (i : Fin 4) :
    coeffL1 (C u * (X i - C v) : MvPolynomial (Fin 4) ℝ) ≤ |u| * (1 + |v|) := by
  apply (coeffL1_C_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (coeffL1_sub_le _ _).trans
  rw [coeffL1_X, coeffL1_C]

theorem coeffL1_subst_le (i : Fin 4) : coeffL1 (Z.subst i) ≤ Z.liftBudget := by
  have hq : 0 ≤ |Z.q⁻¹| * (1 + |Z.t₀| + |Z.z₀|) := by positivity
  have hw : 0 ≤ |Z.w⁻¹| * (1 + |Z.c₂| + |Z.c₃| + |Z.c₄|) := by positivity
  have hh : 0 ≤ |Z.a⁻¹| * (1 + |Z.h₀|) := by positivity
  have ht0 := abs_nonneg Z.t₀
  have hz0 := abs_nonneg Z.z₀
  have hqi := abs_nonneg Z.q⁻¹
  fin_cases i
  · have := coeffL1_C_mul_sub_C Z.q⁻¹ Z.t₀ 0
    simp only [subst, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at this ⊢
    simp only [liftBudget]
    nlinarith
  · have := coeffL1_C_mul_sub_C Z.q⁻¹ Z.z₀ 1
    simp only [subst, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at this ⊢
    simp only [liftBudget]
    nlinarith
  · simp only [subst, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    apply (coeffL1_C_mul_le _ _).trans
    have h0 := coeffL1_sub_le (X 2 - C Z.c₂ - C Z.c₃ * X 0 : MvPolynomial (Fin 4) ℝ) (C Z.c₄ * X 1)
    have h1 := coeffL1_sub_le (X 2 - C Z.c₂ : MvPolynomial (Fin 4) ℝ) (C Z.c₃ * X 0)
    have h2 := coeffL1_sub_le (X 2 : MvPolynomial (Fin 4) ℝ) (C Z.c₂)
    have h3 := coeffL1_C_mul_le Z.c₃ (X (0 : Fin 4))
    have h4 := coeffL1_C_mul_le Z.c₄ (X (1 : Fin 4))
    simp only [coeffL1_X, coeffL1_C, mul_one] at h0 h1 h2 h3 h4
    have hb : coeffL1 (X 2 - C Z.c₂ - C Z.c₃ * X 0 - C Z.c₄ * X 1 : MvPolynomial (Fin 4) ℝ) ≤
        1 + |Z.c₂| + |Z.c₃| + |Z.c₄| := by linarith
    have := mul_le_mul_of_nonneg_left hb (abs_nonneg Z.w⁻¹)
    simp only [liftBudget]
    linarith
  · have := coeffL1_C_mul_sub_C Z.a⁻¹ Z.h₀ 3
    simp only [subst, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val] at this ⊢
    simp only [liftBudget]
    linarith

/-- Coefficients of a lifted test of degree at most two. -/
theorem coeff_lift_le (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (e : Fin 4 →₀ ℕ) :
    |(Z.lift Q).coeff e| ≤ |Z.a| * coeffL1 Q * Z.liftBudget ^ 2 := by
  apply (abs_coeff_le_coeffL1 _ _).trans
  apply (coeffL1_C_mul_le _ _).trans
  have hb := coeffL1_bind₁_le Z.subst Z.liftBudget one_le_liftBudget coeffL1_subst_le Q
  calc
    _ ≤ |Z.a| * (coeffL1 Q * Z.liftBudget ^ Q.totalDegree) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ ≤ |Z.a| * (coeffL1 Q * Z.liftBudget ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_liftBudget hQ)
          (coeffL1_nonneg Q)) (abs_nonneg _)
    _ = _ := by ring

/-- An `ℓ¹` bound for the original coordinates as zoomed polynomials. -/
def pushBudget : ℝ :=
  1 + (|Z.t₀| + |Z.q|) + (|Z.z₀| + |Z.q|) +
    (|Z.c₂| + |Z.c₃| * (|Z.t₀| + |Z.q|) + |Z.c₄| * (|Z.z₀| + |Z.q|) + |Z.w|) +
    (|Z.h₀| + |Z.a|)

theorem one_le_pushBudget : 1 ≤ Z.pushBudget := by
  simp only [pushBudget]
  have := abs_nonneg Z.t₀
  have := abs_nonneg Z.q
  have := abs_nonneg Z.z₀
  have := abs_nonneg Z.c₂
  have := abs_nonneg Z.w
  have := abs_nonneg Z.h₀
  have := abs_nonneg Z.a
  have : 0 ≤ |Z.c₃| * (|Z.t₀| + |Z.q|) := by positivity
  have : 0 ≤ |Z.c₄| * (|Z.z₀| + |Z.q|) := by positivity
  linarith

theorem coeffL1_C_add_C_mul_X (u v : ℝ) (i : Fin 4) :
    coeffL1 (C u + C v * X i : MvPolynomial (Fin 4) ℝ) ≤ |u| + |v| := by
  apply (coeffL1_add_le _ _).trans
  have := coeffL1_C_mul_le v (X i : MvPolynomial (Fin 4) ℝ)
  rw [coeffL1_X, mul_one] at this
  rw [coeffL1_C]
  linarith

theorem coeffL1_unsubst_le (i : Fin 4) : coeffL1 (Z.unsubst i) ≤ Z.pushBudget := by
  have h0 := coeffL1_C_add_C_mul_X Z.t₀ Z.q 0
  have h1 := coeffL1_C_add_C_mul_X Z.z₀ Z.q 1
  have h3 := coeffL1_C_add_C_mul_X Z.h₀ Z.a 3
  have hc3 := abs_nonneg Z.c₃
  have hc4 := abs_nonneg Z.c₄
  have e1 : 0 ≤ |Z.c₃| * (|Z.t₀| + |Z.q|) := by positivity
  have e2 : 0 ≤ |Z.c₄| * (|Z.z₀| + |Z.q|) := by positivity
  have := abs_nonneg Z.c₂
  have := abs_nonneg Z.w
  have := abs_nonneg Z.h₀
  have := abs_nonneg Z.a
  have := abs_nonneg Z.t₀
  have := abs_nonneg Z.q
  have := abs_nonneg Z.z₀
  fin_cases i
  · simp only [unsubst, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    simp only [pushBudget]
    linarith
  · simp only [unsubst, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    simp only [pushBudget]
    linarith
  · simp only [unsubst, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    have a1 := coeffL1_add_le
      (C Z.c₂ + C Z.c₃ * (C Z.t₀ + C Z.q * X 0) + C Z.c₄ * (C Z.z₀ + C Z.q * X 1) :
        MvPolynomial (Fin 4) ℝ) (C Z.w * X 2)
    have a2 := coeffL1_add_le
      (C Z.c₂ + C Z.c₃ * (C Z.t₀ + C Z.q * X 0) : MvPolynomial (Fin 4) ℝ)
      (C Z.c₄ * (C Z.z₀ + C Z.q * X 1))
    have a3 := coeffL1_add_le (C Z.c₂ : MvPolynomial (Fin 4) ℝ)
      (C Z.c₃ * (C Z.t₀ + C Z.q * X 0))
    have b1 := coeffL1_C_mul_le Z.c₃ (C Z.t₀ + C Z.q * X 0 : MvPolynomial (Fin 4) ℝ)
    have b2 := coeffL1_C_mul_le Z.c₄ (C Z.z₀ + C Z.q * X 1 : MvPolynomial (Fin 4) ℝ)
    have b3 := coeffL1_C_mul_le Z.w (X (2 : Fin 4))
    rw [coeffL1_X, mul_one] at b3
    rw [coeffL1_C] at a3
    have c1 := mul_le_mul_of_nonneg_left h0 hc3
    have c2 := mul_le_mul_of_nonneg_left h1 hc4
    simp only [pushBudget]
    linarith
  · simp only [unsubst, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp only [pushBudget]
    linarith

/-- Coefficients of a pushed test of degree at most two. -/
theorem coeffL1_push_le (F : MvPolynomial (Fin 4) ℝ) (hF : F.totalDegree ≤ 2) :
    coeffL1 (Z.push F) ≤ |Z.a⁻¹| * coeffL1 F * Z.pushBudget ^ 2 := by
  apply (coeffL1_C_mul_le _ _).trans
  have hb := coeffL1_bind₁_le Z.unsubst Z.pushBudget one_le_pushBudget coeffL1_unsubst_le F
  calc
    _ ≤ |Z.a⁻¹| * (coeffL1 F * Z.pushBudget ^ F.totalDegree) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ ≤ |Z.a⁻¹| * (coeffL1 F * Z.pushBudget ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_pushBudget hF)
          (coeffL1_nonneg F)) (abs_nonneg _)
    _ = _ := by ring

end Zoom

end

end Submission.Lib.K4ContactTransfer
