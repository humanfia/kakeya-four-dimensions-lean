import Mathlib
import Submission.Obl.k4_scalar_true_terminal_lifting.Interface

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-!
# The chart maps `θ` act polynomially on coefficients

If `θ` transports the graphs `t ↦ (y l t, x l t)` by the affine reparametrisation
`t ↦ (t - t₀) / dt` (with `dt ≠ 0`), the affine shear `y ↦ (y - u - t v) / J` and the
quadratic correction `x ↦ (x - P(t, y)) / s` (with `P` of total degree `≤ 2`), then the
coefficient vector `(θ l).2` is a polynomial map of total degree `≤ 2` of `l.2`.

The coefficients are recovered by evaluating at the parameters `σ = 0, 1, -1`, i.e. at
`t = t₀, t₀ + dt, t₀ - dt`.
-/

/-! ### Total degree bounds -/

/-- Substituting polynomials of total degree `≤ e` into a polynomial `p` gives total degree
`≤ p.totalDegree * e`. -/
theorem theta_totalDegree_bind₁_le {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (e : ℕ)
    (hf : ∀ i, (f i).totalDegree ≤ e) :
    (bind₁ f p).totalDegree ≤ p.totalDegree * e := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le (fun d hd => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (f i ^ d i).totalDegree
      ≤ ∑ i ∈ d.support, d i * e :=
        Finset.sum_le_sum (fun i _ => (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (∑ i ∈ d.support, d i) * e := by rw [Finset.sum_mul]
    _ ≤ p.totalDegree * e := Nat.mul_le_mul_right _ (le_totalDegree hd)

theorem theta_deg_add {σ : Type*} {n : ℕ} {a b : MvPolynomial σ ℝ}
    (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) : (a + b).totalDegree ≤ n :=
  (totalDegree_add a b).trans (max_le ha hb)

theorem theta_deg_sub {σ : Type*} {n : ℕ} {a b : MvPolynomial σ ℝ}
    (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) : (a - b).totalDegree ≤ n :=
  (totalDegree_sub a b).trans (max_le ha hb)

theorem theta_deg_C_mul {σ : Type*} {n : ℕ} (c : ℝ) {b : MvPolynomial σ ℝ}
    (hb : b.totalDegree ≤ n) : (C c * b).totalDegree ≤ n :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact hb)

theorem theta_deg_C {σ : Type*} {n : ℕ} (c : ℝ) : (C c : MvPolynomial σ ℝ).totalDegree ≤ n := by
  rw [totalDegree_C]; exact Nat.zero_le _

theorem theta_deg_X {σ : Type*} {n : ℕ} (i : σ) (hn : 1 ≤ n) :
    (X i : MvPolynomial σ ℝ).totalDegree ≤ n := by
  rw [totalDegree_X]; exact hn

/-- Evaluation commutes with substitution. -/
theorem theta_eval_bind₁ {σ τ : Type*} (a : τ → ℝ) (g : σ → MvPolynomial τ ℝ)
    (P : MvPolynomial σ ℝ) : eval a (bind₁ g P) = eval (fun i => eval a (g i)) P :=
  eval₂Hom_bind₁ (RingHom.id ℝ) a g P

/-! ### The coefficient polynomials -/

/-- The polynomial `l.2 ↦ (y l τ - u - τ v) / J`. -/
noncomputable def theta_YY (u v J τ : ℝ) : MvPolynomial (Fin 5) ℝ :=
  C J⁻¹ * (X 0 + C τ * X 1 - C u - C (τ * v))

/-- The polynomial `l.2 ↦ P (τ, y l τ)`. -/
noncomputable def theta_PP (P : MvPolynomial (Fin 2) ℝ) (τ : ℝ) : MvPolynomial (Fin 5) ℝ :=
  bind₁ (![C τ, X 0 + C τ * X 1] : Fin 2 → MvPolynomial (Fin 5) ℝ) P

/-- The polynomial `l.2 ↦ (x l τ - P (τ, y l τ)) / s`. -/
noncomputable def theta_XX (P : MvPolynomial (Fin 2) ℝ) (s τ : ℝ) : MvPolynomial (Fin 5) ℝ :=
  C s⁻¹ * (X 2 + C τ * X 3 + C (τ ^ 2) * X 4 - theta_PP P τ)

theorem theta_eval_YY (a : Fin 5 → ℝ) (u v J τ : ℝ) :
    eval a (theta_YY u v J τ) = J⁻¹ * (a 0 + τ * a 1 - u - τ * v) := by
  simp only [theta_YY, map_mul, map_sub, map_add, eval_C, eval_X]

theorem theta_eval_PP (a : Fin 5 → ℝ) (P : MvPolynomial (Fin 2) ℝ) (τ : ℝ) :
    eval a (theta_PP P τ) = eval ![τ, a 0 + τ * a 1] P := by
  rw [theta_PP, theta_eval_bind₁]
  have h : (fun i => eval a ((![C τ, X 0 + C τ * X 1] : Fin 2 → MvPolynomial (Fin 5) ℝ) i)) =
      ![τ, a 0 + τ * a 1] := by
    funext i
    fin_cases i <;> simp
  rw [h]

theorem theta_eval_XX (a : Fin 5 → ℝ) (P : MvPolynomial (Fin 2) ℝ) (s τ : ℝ) :
    eval a (theta_XX P s τ) =
      s⁻¹ * (a 2 + τ * a 3 + τ ^ 2 * a 4 - eval ![τ, a 0 + τ * a 1] P) := by
  simp only [theta_XX, map_mul, map_sub, map_add, eval_C, eval_X, theta_eval_PP]

theorem theta_deg_YY (u v J τ : ℝ) : (theta_YY u v J τ).totalDegree ≤ 2 := by
  unfold theta_YY
  exact theta_deg_C_mul _ (theta_deg_sub (theta_deg_sub (theta_deg_add (theta_deg_X _ (by norm_num))
    (theta_deg_C_mul _ (theta_deg_X _ (by norm_num)))) (theta_deg_C _)) (theta_deg_C _))

theorem theta_deg_PP (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (τ : ℝ) :
    (theta_PP P τ).totalDegree ≤ 2 := by
  unfold theta_PP
  refine (theta_totalDegree_bind₁_le _ P 1 ?_).trans ?_
  · intro i
    fin_cases i
    · exact theta_deg_C _
    · exact theta_deg_add (theta_deg_X _ le_rfl) (theta_deg_C_mul _ (theta_deg_X _ le_rfl))
  · rw [Nat.mul_one]; exact hP

theorem theta_deg_XX (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) (s τ : ℝ) :
    (theta_XX P s τ).totalDegree ≤ 2 := by
  unfold theta_XX
  exact theta_deg_C_mul _ (theta_deg_sub (theta_deg_add (theta_deg_add
    (theta_deg_X _ (by norm_num)) (theta_deg_C_mul _ (theta_deg_X _ (by norm_num))))
    (theta_deg_C_mul _ (theta_deg_X _ (by norm_num)))) (theta_deg_PP P hP τ))

/-! ### The main statements -/

theorem theta_poly (θ : ℕ × (Fin 5 → ℝ) → ℕ × (Fin 5 → ℝ)) (t₀ dt u v J s : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (hdt : dt ≠ 0) (hP : P.totalDegree ≤ 2)
    (hy : ∀ l t, y (θ l) ((t - t₀) / dt) = (y l t - u - t * v) / J)
    (hx : ∀ l t, x (θ l) ((t - t₀) / dt) = (x l t - MvPolynomial.eval ![t, y l t] P) / s) :
    ∃ Q : Fin 5 → MvPolynomial (Fin 5) ℝ, (∀ e, (Q e).totalDegree ≤ 2) ∧
      ∀ l e, (θ l).2 e = MvPolynomial.eval l.2 (Q e) := by
  refine ⟨![theta_YY u v J t₀, theta_YY u v J (t₀ + dt) - theta_YY u v J t₀,
    theta_XX P s t₀, C (1 / 2) * (theta_XX P s (t₀ + dt) - theta_XX P s (t₀ - dt)),
    C (1 / 2) * (theta_XX P s (t₀ + dt) + theta_XX P s (t₀ - dt)) - theta_XX P s t₀], ?_, ?_⟩
  · intro e
    fin_cases e
    · exact theta_deg_YY _ _ _ _
    · exact theta_deg_sub (theta_deg_YY _ _ _ _) (theta_deg_YY _ _ _ _)
    · exact theta_deg_XX P hP _ _
    · exact theta_deg_C_mul _ (theta_deg_sub (theta_deg_XX P hP _ _) (theta_deg_XX P hP _ _))
    · exact theta_deg_sub (theta_deg_C_mul _ (theta_deg_add (theta_deg_XX P hP _ _)
        (theta_deg_XX P hP _ _))) (theta_deg_XX P hP _ _)
  · intro l e
    have e0 : (t₀ - t₀) / dt = 0 := by rw [sub_self, zero_div]
    have e1 : (t₀ + dt - t₀) / dt = 1 := by rw [add_sub_cancel_left, div_self hdt]
    have em : (t₀ - dt - t₀) / dt = -1 := by
      rw [sub_sub_cancel_left, neg_div, div_self hdt]
    have hy0 := hy l t₀
    have hy1 := hy l (t₀ + dt)
    have hx0 := hx l t₀
    have hx1 := hx l (t₀ + dt)
    have hxm := hx l (t₀ - dt)
    rw [e0] at hy0 hx0
    rw [e1] at hy1 hx1
    rw [em] at hxm
    simp only [y, x] at hy0 hy1 hx0 hx1 hxm
    fin_cases e
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, theta_eval_YY]
      linear_combination hy0
    · simp [theta_eval_YY]
      linear_combination hy1 - hy0
    · simp [theta_eval_XX]
      linear_combination hx0
    · simp [theta_eval_XX]
      linear_combination (1 / 2 : ℝ) * hx1 - (1 / 2 : ℝ) * hxm
    · simp [theta_eval_XX]
      linear_combination (1 / 2 : ℝ) * hx1 + (1 / 2 : ℝ) * hxm - hx0

theorem theta_poly6 (θ : ℕ × (Fin 5 → ℝ) → ℕ × (Fin 5 → ℝ)) (t₀ dt u v J s : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) (hdt : dt ≠ 0) (hP : P.totalDegree ≤ 2)
    (hy : ∀ l t, y (θ l) ((t - t₀) / dt) = (y l t - u - t * v) / J)
    (hx : ∀ l t, x (θ l) ((t - t₀) / dt) = (x l t - MvPolynomial.eval ![t, y l t] P) / s) :
    ∃ Ψ : Fin 6 → MvPolynomial (Fin 6) ℝ, (∀ e, (Ψ e).totalDegree ≤ 2) ∧
      ∀ (z : ℕ) (b : Fin 6 → ℝ),
        (fun e : Fin 5 => MvPolynomial.eval b (Ψ e.castSucc)) = (θ (z, fun e : Fin 5 => b e.castSucc)).2 ∧
        MvPolynomial.eval b (Ψ 5) = (b 5 - t₀) / dt := by
  obtain ⟨Q, hQdeg, hQ⟩ := theta_poly θ t₀ dt u v J s P hdt hP hy hx
  refine ⟨Fin.snoc (α := fun _ => MvPolynomial (Fin 6) ℝ)
    (fun e : Fin 5 => rename Fin.castSucc (Q e)) (C dt⁻¹ * (X 5 - C t₀)), ?_, ?_⟩
  · intro e
    refine Fin.lastCases ?_ (fun i => ?_) e
    · rw [Fin.snoc_last]
      exact theta_deg_C_mul _ (theta_deg_sub (theta_deg_X _ (by norm_num)) (theta_deg_C _))
    · rw [Fin.snoc_castSucc]
      exact (totalDegree_rename_le _ _).trans (hQdeg i)
  · intro z b
    refine ⟨?_, ?_⟩
    · funext e
      rw [Fin.snoc_castSucc, eval_rename, hQ]
      rfl
    · show eval b (Fin.snoc (α := fun _ => MvPolynomial (Fin 6) ℝ)
        (fun e : Fin 5 => rename Fin.castSucc (Q e)) (C dt⁻¹ * (X 5 - C t₀)) (Fin.last 5)) = _
      rw [Fin.snoc_last]
      simp only [map_mul, map_sub, eval_C, eval_X]
      rw [div_eq_inv_mul]

end Submission.Obl.k4_scalar_true_terminal_lifting
