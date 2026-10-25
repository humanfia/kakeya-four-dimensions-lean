import Submission.Obl.k4_scalar_true_terminal_lifting.LiftDefs

/-!
# Lifted chart: algebraic clauses

Time budget, count, widths, affine fit coefficients, the residual polynomial (degree and
coefficients), assignment bounds and the two trajectory fits of the lifted chart.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

namespace RefStep

variable {p q : Code} {r b : ℝ} {k K : ℕ} (S : RefStep p q r b k K)
variable {B₂ : ℕ} {h₂ ε₂ : ℝ} (Q : ChartW q B₂ (L q) (L q) h₂ ε₂ true k)

/-! ### Clauses of the two charts -/

/-- The time clause of the parent chart. -/
lemma alg_S_time : (2 : ℝ) ^ S.T₁ ≤ N p K ^ S.h₁ := by
  have h := S.hcd
  unfold ChartData at h
  exact h.1

/-- The piece clauses of the parent chart used for the lifted chart. -/
lemma alg_S_piece (i : Fin (W q k)) :
    0 < S.J₁ i ∧ (S.J₁ i)⁻¹ ≤ N p K ^ (S.B₁ : ℝ) ∧ S.J₁ i ≤ N p K ^ S.ε₁ / (2 : ℝ) ^ S.T₁ ∧
    |S.u₁ i| + |S.v₁ i| ≤ N p K ^ S.ε₁ ∧ (S.P₁ i).totalDegree ≤ 2 ∧
    (∀ a, |(S.P₁ i).coeff a| ≤ N p K ^ (S.B₁ : ℝ)) ∧
    (∀ l ∈ S.A₁ i, (l.1 : ℝ) ≤ N p K ^ (S.B₁ : ℝ) ∧ ∀ e, |l.2 e| ≤ N p K ^ S.ε₁) := by
  have h := S.hcd
  unfold ChartData at h
  obtain ⟨-, -, -, -, -, h6, -⟩ := h
  obtain ⟨-, c2, c3, c4, c5, c6, c7, c8, -⟩ := h6 i
  exact ⟨c2, c3, c4, c5, c6, c7, c8⟩

include S in
/-- The time and count clauses of the q-chart, at the parent index. -/
lemma alg_Q_time_count : (2 : ℝ) ^ Q.T ≤ N p K ^ h₂ ∧ (Q.n : ℝ) ≤ N p K ^ (B₂ : ℝ) := by
  have h := Q.hcd
  unfold ChartData at h
  obtain ⟨h1, h2, -⟩ := h
  rw [S.hN] at h1 h2
  exact ⟨h1, h2⟩

include S in
/-- The piece clauses of the q-chart used for the lifted chart, at the parent index. -/
lemma alg_Q_piece (d : Fin Q.n) :
    0 < Q.J d ∧ (Q.J d)⁻¹ ≤ N p K ^ (B₂ : ℝ) ∧ Q.J d ≤ N p K ^ ε₂ / (2 : ℝ) ^ Q.T ∧
    |Q.u d| + |Q.v d| ≤ N p K ^ ε₂ ∧ (Q.P d).totalDegree ≤ 2 ∧
    (∀ a, |(Q.P d).coeff a| ≤ N p K ^ (B₂ : ℝ)) ∧
    (∀ l ∈ Q.A d, ∀ t ∈ I Q.T (Q.j d),
      |y l t - Q.u d - t * Q.v d| ≤ N p K ^ ε₂ * Q.J d ∧
      |x l t - MvPolynomial.eval ![t, y l t] (Q.P d)| ≤ N p K ^ ε₂ * N p K ^ (-L q)) := by
  have h := Q.hcd
  unfold ChartData at h
  obtain ⟨-, -, -, -, -, h6, -⟩ := h
  obtain ⟨-, c2, c3, c4, c5, c6, c7, -, -, -, c11, -⟩ := h6 d
  rw [S.hN] at c3 c4 c5 c7 c11
  exact ⟨c2, c3, c4, c5, c6, c7, c11⟩

/-! ### The affine normalization -/

lemma alg_G_zero (i : Fin (W q k)) : S.G i 0 = C S.dt⁻¹ * (X 0 - C (S.t₀ i)) := rfl

lemma alg_G_one (i : Fin (W q k)) :
    S.G i 1 = C (S.J₁ i)⁻¹ * (X 1 - C (S.u₁ i) - C (S.v₁ i) * X 0) := rfl

/-- The affine normalization has degree at most one. -/
lemma alg_G_deg (i : Fin (W q k)) (e : Fin 2) : (S.G i e).totalDegree ≤ 1 := by
  have hX : ∀ j : Fin 2, (X j : MvPolynomial (Fin 2) ℝ).totalDegree = 1 := fun j => totalDegree_X j
  fin_cases e
  · show (S.G i 0).totalDegree ≤ 1
    rw [alg_G_zero]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_sub_C_le _ _).trans ?_
    rw [hX]
  · show (S.G i 1).totalDegree ≤ 1
    rw [alg_G_one]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_sub_C_le _ _).trans ?_
      rw [hX]
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add, hX]

/-- Coefficient norms of the affine normalization. -/
lemma alg_G_cnorm (hN : 1 ≤ N p K) (hε₁ : S.ε₁ ≤ 1) (i : Fin (W q k)) (e : Fin 2) :
    cnorm (S.G i e) ≤ 2 * N p K ^ (S.B₁ + 1) := by
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  obtain ⟨hJ1, hJ1i, hJ1le, huv1, -⟩ := S.alg_S_piece i
  rw [Real.rpow_natCast] at hJ1i
  have hE1 : N p K ^ S.ε₁ ≤ N p K := by
    calc N p K ^ S.ε₁ ≤ N p K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hε₁
      _ = N p K := Real.rpow_one _
  have hM : (0 : ℝ) < 2 ^ S.T₁ := by positivity
  have hpow : N p K ^ (S.B₁ + 1) = N p K ^ S.B₁ * N p K := pow_succ _ _
  have hNB : 0 ≤ N p K ^ S.B₁ := pow_nonneg hN0.le _
  fin_cases e
  · show cnorm (S.G i 0) ≤ 2 * N p K ^ (S.B₁ + 1)
    rw [alg_G_zero]
    have h2T : (2 : ℝ) ^ S.T₁ ≤ N p K ^ S.B₁ * N p K := by
      have h1 : S.J₁ i * 2 ^ S.T₁ ≤ N p K ^ S.ε₁ := (le_div_iff₀ hM).1 hJ1le
      have h2 : (2 : ℝ) ^ S.T₁ ≤ N p K ^ S.ε₁ * (S.J₁ i)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hJ1]
        linarith
      calc (2 : ℝ) ^ S.T₁ ≤ N p K ^ S.ε₁ * (S.J₁ i)⁻¹ := h2
        _ ≤ N p K * N p K ^ S.B₁ := mul_le_mul hE1 hJ1i (inv_nonneg.2 hJ1.le) hN0.le
        _ = N p K ^ S.B₁ * N p K := mul_comm _ _
    have ht0 := S.t₀_nonneg i
    have ht1 := S.t₀_le_one i
    calc cnorm (C S.dt⁻¹ * (X 0 - C (S.t₀ i)) : MvPolynomial (Fin 2) ℝ)
        ≤ |S.dt⁻¹| * cnorm (X 0 - C (S.t₀ i) : MvPolynomial (Fin 2) ℝ) := cnorm_C_mul_le _ _
      _ ≤ |S.dt⁻¹| * (cnorm (X 0 : MvPolynomial (Fin 2) ℝ) +
            cnorm (C (S.t₀ i) : MvPolynomial (Fin 2) ℝ)) :=
          mul_le_mul_of_nonneg_left (cnorm_sub_le _ _) (abs_nonneg _)
      _ = 2 ^ S.T₁ * (1 + S.t₀ i) := by
          rw [cnorm_X, cnorm_C, abs_of_nonneg ht0, dt, inv_inv, abs_of_pos hM]
      _ ≤ 2 ^ S.T₁ * 2 := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          linarith
      _ ≤ 2 * N p K ^ (S.B₁ + 1) := by
          rw [hpow]
          linarith
  · show cnorm (S.G i 1) ≤ 2 * N p K ^ (S.B₁ + 1)
    rw [alg_G_one]
    calc cnorm (C (S.J₁ i)⁻¹ * (X 1 - C (S.u₁ i) - C (S.v₁ i) * X 0) : MvPolynomial (Fin 2) ℝ)
        ≤ |(S.J₁ i)⁻¹| * cnorm (X 1 - C (S.u₁ i) - C (S.v₁ i) * X 0 : MvPolynomial (Fin 2) ℝ) :=
          cnorm_C_mul_le _ _
      _ ≤ |(S.J₁ i)⁻¹| * (1 + |S.u₁ i| + |S.v₁ i|) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc cnorm (X 1 - C (S.u₁ i) - C (S.v₁ i) * X 0 : MvPolynomial (Fin 2) ℝ)
              ≤ cnorm (X 1 - C (S.u₁ i) : MvPolynomial (Fin 2) ℝ) +
                  cnorm (C (S.v₁ i) * X 0 : MvPolynomial (Fin 2) ℝ) := cnorm_sub_le _ _
            _ ≤ (cnorm (X 1 : MvPolynomial (Fin 2) ℝ) +
                  cnorm (C (S.u₁ i) : MvPolynomial (Fin 2) ℝ)) +
                  |S.v₁ i| * cnorm (X 0 : MvPolynomial (Fin 2) ℝ) :=
                add_le_add (cnorm_sub_le _ _) (cnorm_C_mul_le _ _)
            _ = 1 + |S.u₁ i| + |S.v₁ i| := by rw [cnorm_X, cnorm_X, cnorm_C, mul_one]
      _ ≤ N p K ^ S.B₁ * (1 + N p K) := by
          rw [abs_of_pos (inv_pos.2 hJ1)]
          apply mul_le_mul hJ1i _ (by positivity) hNB
          linarith
      _ ≤ 2 * N p K ^ (S.B₁ + 1) := by
          rw [hpow]
          nlinarith

/-! ### Algebra of the lifted fits -/

/-- The scalar fit of the lifted chart is the normalized scalar fit, rescaled. -/
lemma alg_fit_y (i : Fin (W q k)) (u₂ v₂ : ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ)
    (hJ : S.J₁ i ≠ 0) :
    y l t - (S.u₁ i + S.J₁ i * u₂ - S.J₁ i * v₂ * (S.t₀ i / S.dt)) -
        t * (S.v₁ i + S.J₁ i * v₂ / S.dt) =
      S.J₁ i * (y (S.θ i l) ((t - S.t₀ i) / S.dt) - u₂ - (t - S.t₀ i) / S.dt * v₂) := by
  rw [S.hy i l t]
  have hdt : S.dt ≠ 0 := S.dt_pos.ne'
  field_simp
  ring

/-- The residual of the lifted chart is the normalized residual, rescaled. -/
lemma alg_fit_x (d : Fin Q.n) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) (hNr : N p K ^ (-r) ≠ 0) :
    x l t - MvPolynomial.eval ![t, y l t] (S.P₃ Q d) =
      N p K ^ (-r) * (x (S.θ (Q.γ d) l) ((t - S.t₀ (Q.γ d)) / S.dt) -
        MvPolynomial.eval ![(t - S.t₀ (Q.γ d)) / S.dt,
          y (S.θ (Q.γ d) l) ((t - S.t₀ (Q.γ d)) / S.dt)] (Q.P d)) := by
  rw [S.eval_P₃ Q d, S.hx (Q.γ d) l t, S.hy (Q.γ d) l t]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- The bound on the lifted affine fit coefficients. -/
lemma alg_uv_bound (hN : 1 ≤ N p K) (i : Fin (W q k)) (u₂ v₂ : ℝ) {E₂ : ℝ} (hE₂ : 1 ≤ E₂)
    (huv : |u₂| + |v₂| ≤ E₂) :
    |S.u₁ i + S.J₁ i * u₂ - S.J₁ i * v₂ * (S.t₀ i / S.dt)| +
      |S.v₁ i + S.J₁ i * v₂ / S.dt| ≤ 3 * (N p K ^ S.ε₁ * E₂) := by
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  obtain ⟨hJ1, -, hJ1le, huv1, -⟩ := S.alg_S_piece i
  have hM : (0 : ℝ) < 2 ^ S.T₁ := by positivity
  have hM1 : (1 : ℝ) ≤ 2 ^ S.T₁ := one_le_pow₀ (by norm_num)
  have hj : ((S.j₁ i : ℕ) : ℝ) + 1 ≤ 2 ^ S.T₁ := by
    have := (S.j₁ i).isLt
    exact_mod_cast this
  have hj0 : (0 : ℝ) ≤ ((S.j₁ i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJM : S.J₁ i * 2 ^ S.T₁ ≤ N p K ^ S.ε₁ := (le_div_iff₀ hM).1 hJ1le
  have hE1 : 0 ≤ N p K ^ S.ε₁ := Real.rpow_nonneg hN0.le _
  have hdiv : S.J₁ i * v₂ / S.dt = S.J₁ i * v₂ * 2 ^ S.T₁ := by
    rw [dt, div_inv_eq_mul]
  rw [S.t₀_div_dt, hdiv]
  have t1 : |S.u₁ i + S.J₁ i * u₂ - S.J₁ i * v₂ * ((S.j₁ i : ℕ) : ℝ)| ≤
      |S.u₁ i| + S.J₁ i * |u₂| + S.J₁ i * |v₂| * ((S.j₁ i : ℕ) : ℝ) := by
    calc _ ≤ |S.u₁ i + S.J₁ i * u₂| + |S.J₁ i * v₂ * ((S.j₁ i : ℕ) : ℝ)| := abs_sub _ _
      _ ≤ |S.u₁ i| + |S.J₁ i * u₂| + |S.J₁ i * v₂ * ((S.j₁ i : ℕ) : ℝ)| := by
          gcongr
          exact abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_of_pos hJ1, abs_of_nonneg hj0]
  have t2 : |S.v₁ i + S.J₁ i * v₂ * 2 ^ S.T₁| ≤ |S.v₁ i| + S.J₁ i * |v₂| * 2 ^ S.T₁ := by
    calc _ ≤ |S.v₁ i| + |S.J₁ i * v₂ * 2 ^ S.T₁| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hJ1, abs_of_pos hM]
  have hJ1E : S.J₁ i ≤ N p K ^ S.ε₁ := by nlinarith
  have hJjE : S.J₁ i * ((S.j₁ i : ℕ) : ℝ) ≤ N p K ^ S.ε₁ := by nlinarith
  have b1 : S.J₁ i * |u₂| ≤ N p K ^ S.ε₁ * |u₂| :=
    mul_le_mul_of_nonneg_right hJ1E (abs_nonneg _)
  have b2 : S.J₁ i * |v₂| * ((S.j₁ i : ℕ) : ℝ) ≤ N p K ^ S.ε₁ * |v₂| := by
    nlinarith [abs_nonneg v₂]
  have b3 : S.J₁ i * |v₂| * 2 ^ S.T₁ ≤ N p K ^ S.ε₁ * |v₂| := by
    nlinarith [abs_nonneg v₂]
  have b4 : N p K ^ S.ε₁ * (|u₂| + |v₂|) ≤ N p K ^ S.ε₁ * E₂ :=
    mul_le_mul_of_nonneg_left huv hE1
  have b5 : N p K ^ S.ε₁ ≤ N p K ^ S.ε₁ * E₂ := le_mul_of_one_le_right hE1 hE₂
  nlinarith [abs_nonneg u₂, abs_nonneg v₂]

/-! ### The clauses -/

lemma lift_time (hN : 0 < N p K) : (2 : ℝ) ^ (S.T₁ + Q.T) ≤ N p K ^ (S.h₁ + h₂) := by
  rw [pow_add, Real.rpow_add hN]
  exact mul_le_mul S.alg_S_time (S.alg_Q_time_count Q).1 (by positivity)
    (Real.rpow_nonneg hN.le _)

lemma lift_count (hN : 1 ≤ N p K) :
    (Q.n : ℝ) ≤ N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ) := by
  refine (S.alg_Q_time_count Q).2.trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
  exact_mod_cast (by omega : B₂ ≤ 2 * B₂ + 2 * S.B₁ + 9)

lemma lift_J_pos (d : Fin Q.n) : 0 < S.J₃ Q d :=
  mul_pos (S.alg_S_piece (Q.γ d)).1 (S.alg_Q_piece Q d).1

lemma lift_J_inv (hN : 1 ≤ N p K) (d : Fin Q.n) :
    (S.J₃ Q d)⁻¹ ≤ N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ) := by
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  obtain ⟨hJ1, hJ1i, -⟩ := S.alg_S_piece (Q.γ d)
  obtain ⟨hJ2, hJ2i, -⟩ := S.alg_Q_piece Q d
  rw [J₃, mul_inv]
  calc (S.J₁ (Q.γ d))⁻¹ * (Q.J d)⁻¹ ≤ N p K ^ (S.B₁ : ℝ) * N p K ^ (B₂ : ℝ) :=
        mul_le_mul hJ1i hJ2i (inv_nonneg.2 hJ2.le) (Real.rpow_nonneg hN0.le _)
    _ = N p K ^ ((S.B₁ : ℝ) + B₂) := (Real.rpow_add hN0 _ _).symm
    _ ≤ N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        have h1 : (0 : ℝ) ≤ B₂ := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ S.B₁ := Nat.cast_nonneg _
        push_cast
        linarith

lemma lift_J_le (hN : 1 ≤ N p K) {ε₃ : ℝ} (hε : S.ε₁ + ε₂ ≤ ε₃) (d : Fin Q.n) :
    S.J₃ Q d ≤ N p K ^ ε₃ / (2 : ℝ) ^ (S.T₁ + Q.T) := by
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  obtain ⟨hJ1, -, hJ1le, -⟩ := S.alg_S_piece (Q.γ d)
  obtain ⟨hJ2, -, hJ2le, -⟩ := S.alg_Q_piece Q d
  rw [J₃]
  calc S.J₁ (Q.γ d) * Q.J d
      ≤ (N p K ^ S.ε₁ / (2 : ℝ) ^ S.T₁) * (N p K ^ ε₂ / (2 : ℝ) ^ Q.T) :=
        mul_le_mul hJ1le hJ2le hJ2.le (div_nonneg (Real.rpow_nonneg hN0.le _) (by positivity))
    _ = N p K ^ (S.ε₁ + ε₂) / (2 : ℝ) ^ (S.T₁ + Q.T) := by
        rw [Real.rpow_add hN0, pow_add]
        ring
    _ ≤ N p K ^ ε₃ / (2 : ℝ) ^ (S.T₁ + Q.T) :=
        div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hε) (by positivity)

lemma lift_uv (hN : 1 ≤ N p K) (hε₂ : 0 ≤ ε₂) {ε₃ : ℝ}
    (hε₃ : 4 * N p K ^ (S.ε₁ + ε₂) ≤ N p K ^ ε₃) (d : Fin Q.n) :
    |S.u₃ Q d| + |S.v₃ Q d| ≤ N p K ^ ε₃ := by
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  obtain ⟨-, -, -, huv2, -⟩ := S.alg_Q_piece Q d
  have hE2 : 1 ≤ N p K ^ ε₂ := Real.one_le_rpow hN hε₂
  have hb := S.alg_uv_bound hN (Q.γ d) (Q.u d) (Q.v d) hE2 huv2
  have hE : 0 ≤ N p K ^ S.ε₁ * N p K ^ ε₂ :=
    mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)
  rw [Real.rpow_add hN0] at hε₃
  calc |S.u₃ Q d| + |S.v₃ Q d| ≤ 3 * (N p K ^ S.ε₁ * N p K ^ ε₂) := hb
    _ ≤ N p K ^ ε₃ := by linarith

lemma lift_deg (d : Fin Q.n) : (S.P₃ Q d).totalDegree ≤ 2 := by
  obtain ⟨-, -, -, -, hdeg1, -⟩ := S.alg_S_piece (Q.γ d)
  obtain ⟨-, -, -, -, hdeg2, -⟩ := S.alg_Q_piece Q d
  rw [P₃]
  refine (totalDegree_add _ _).trans (max_le hdeg1 ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_bind₁_le _ (S.alg_G_deg (Q.γ d)) _).trans ?_
  rw [mul_one]
  exact hdeg2

lemma lift_coeff (hN : 2 ≤ N p K) (hr : 0 ≤ r) (hε₁ : S.ε₁ ≤ 1) (d : Fin Q.n)
    (m : Fin 2 →₀ ℕ) :
    |(S.P₃ Q d).coeff m| ≤ N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ) := by
  have hN1 : 1 ≤ N p K := le_trans (by norm_num) hN
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN1
  obtain ⟨-, -, -, -, -, hc1, -⟩ := S.alg_S_piece (Q.γ d)
  obtain ⟨-, -, -, -, hdeg2, hc2, -⟩ := S.alg_Q_piece Q d
  simp only [Real.rpow_natCast] at hc1 hc2 ⊢
  have hR1 : 1 ≤ 2 * N p K ^ (S.B₁ + 1) := by
    have : 1 ≤ N p K ^ (S.B₁ + 1) := one_le_pow₀ hN1
    linarith
  have hP2 : cnorm (Q.P d) ≤ 9 * N p K ^ B₂ := by
    have := cnorm_le_of_coeff (Q.P d) hdeg2 hc2
    norm_num at this
    exact this
  have hbind : cnorm (bind₁ (S.G (Q.γ d)) (Q.P d)) ≤
      9 * N p K ^ B₂ * (2 * N p K ^ (S.B₁ + 1)) ^ 2 := by
    refine (cnorm_bind₁_le _ hR1 (S.alg_G_cnorm hN1 hε₁ (Q.γ d)) _).trans ?_
    exact mul_le_mul hP2 (pow_le_pow_right₀ hR1 hdeg2) (by positivity) (by positivity)
  have hcoef : (S.P₃ Q d).coeff m =
      (S.P₁ (Q.γ d)).coeff m + N p K ^ (-r) * (bind₁ (S.G (Q.γ d)) (Q.P d)).coeff m := by
    simp [P₃, coeff_C_mul]
  have hNr : |N p K ^ (-r)| ≤ 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos hN0 _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (neg_nonpos.2 hr)
  rw [hcoef]
  have hE0 : 0 ≤ N p K ^ (B₂ + 2 * S.B₁ + 2) := pow_nonneg hN0.le _
  have h1 : N p K ^ S.B₁ ≤ N p K ^ (B₂ + 2 * S.B₁ + 2) := pow_le_pow_right₀ hN1 (by omega)
  have h2 : 9 * N p K ^ B₂ * (2 * N p K ^ (S.B₁ + 1)) ^ 2 =
      36 * N p K ^ (B₂ + 2 * S.B₁ + 2) := by ring
  have h3 : (64 : ℝ) ≤ N p K ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 6
    norm_num at this
    exact this
  have h4 : N p K ^ 6 * N p K ^ (B₂ + 2 * S.B₁ + 2) ≤ N p K ^ (2 * B₂ + 2 * S.B₁ + 9) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hN1 (by omega)
  calc |(S.P₁ (Q.γ d)).coeff m + N p K ^ (-r) * (bind₁ (S.G (Q.γ d)) (Q.P d)).coeff m|
      ≤ |(S.P₁ (Q.γ d)).coeff m| +
          |N p K ^ (-r)| * |(bind₁ (S.G (Q.γ d)) (Q.P d)).coeff m| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ N p K ^ S.B₁ + 1 * cnorm (bind₁ (S.G (Q.γ d)) (Q.P d)) :=
        add_le_add (hc1 m) (mul_le_mul hNr (abs_coeff_le_cnorm _ _) (abs_nonneg _) zero_le_one)
    _ ≤ N p K ^ (2 * B₂ + 2 * S.B₁ + 9) := by nlinarith

lemma lift_A_bound (hN : 1 ≤ N p K) {ε₃ : ℝ} (hε : S.ε₁ ≤ ε₃) (d : Fin Q.n) :
    ∀ l ∈ S.A₃ Q d, (l.1 : ℝ) ≤ N p K ^ (((2 * B₂ + 2 * S.B₁ + 9 : ℕ)) : ℝ) ∧
      ∀ e, |l.2 e| ≤ N p K ^ ε₃ := by
  intro l hl
  have hl' : l ∈ S.A₁ (Q.γ d) ∧ S.θ (Q.γ d) l ∈ Q.A d := hl
  obtain ⟨-, -, -, -, -, -, hA⟩ := S.alg_S_piece (Q.γ d)
  obtain ⟨h1, h2⟩ := hA l hl'.1
  refine ⟨h1.trans (Real.rpow_le_rpow_of_exponent_le hN ?_),
    fun e => (h2 e).trans (Real.rpow_le_rpow_of_exponent_le hN hε)⟩
  exact_mod_cast (by omega : S.B₁ ≤ 2 * B₂ + 2 * S.B₁ + 9)

lemma lift_fit (hN : 1 ≤ N p K) (hLq : L q = L p - r) {ε₃ : ℝ} (hε : ε₂ ≤ ε₃)
    (d : Fin Q.n) :
    ∀ l ∈ S.A₃ Q d, ∀ t ∈ I (S.T₁ + Q.T) (S.j₃ Q d),
      |y l t - S.u₃ Q d - t * S.v₃ Q d| ≤ N p K ^ ε₃ * S.J₃ Q d ∧
      |x l t - MvPolynomial.eval ![t, y l t] (S.P₃ Q d)| ≤ N p K ^ ε₃ * N p K ^ (-L p) := by
  intro l hl t ht
  have hN0 : 0 < N p K := lt_of_lt_of_le one_pos hN
  have hl' : l ∈ S.A₁ (Q.γ d) ∧ S.θ (Q.γ d) l ∈ Q.A d := hl
  have hs : (t - S.t₀ (Q.γ d)) / S.dt ∈ I Q.T (Q.j d) :=
    (mem_I_jcomp (S.j₁ (Q.γ d)) (Q.j d) t).1 ht
  obtain ⟨hJ1, -⟩ := S.alg_S_piece (Q.γ d)
  obtain ⟨hJ2, -, -, -, -, -, hfit⟩ := S.alg_Q_piece Q d
  obtain ⟨hfy, hfx⟩ := hfit _ hl'.2 _ hs
  have hNr : 0 < N p K ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hεle : N p K ^ ε₂ ≤ N p K ^ ε₃ := Real.rpow_le_rpow_of_exponent_le hN hε
  constructor
  · have key : y l t - S.u₃ Q d - t * S.v₃ Q d = S.J₁ (Q.γ d) *
        (y (S.θ (Q.γ d) l) ((t - S.t₀ (Q.γ d)) / S.dt) - Q.u d -
          (t - S.t₀ (Q.γ d)) / S.dt * Q.v d) :=
      S.alg_fit_y (Q.γ d) (Q.u d) (Q.v d) l t hJ1.ne'
    rw [key, abs_mul, abs_of_pos hJ1, J₃]
    calc S.J₁ (Q.γ d) * |y (S.θ (Q.γ d) l) ((t - S.t₀ (Q.γ d)) / S.dt) - Q.u d -
          (t - S.t₀ (Q.γ d)) / S.dt * Q.v d|
        ≤ S.J₁ (Q.γ d) * (N p K ^ ε₂ * Q.J d) := mul_le_mul_of_nonneg_left hfy hJ1.le
      _ ≤ S.J₁ (Q.γ d) * (N p K ^ ε₃ * Q.J d) := by
          apply mul_le_mul_of_nonneg_left _ hJ1.le
          exact mul_le_mul_of_nonneg_right hεle hJ2.le
      _ = N p K ^ ε₃ * (S.J₁ (Q.γ d) * Q.J d) := by ring
  · rw [S.alg_fit_x Q d l t hNr.ne', abs_mul, abs_of_pos hNr]
    calc N p K ^ (-r) * |x (S.θ (Q.γ d) l) ((t - S.t₀ (Q.γ d)) / S.dt) -
          MvPolynomial.eval ![(t - S.t₀ (Q.γ d)) / S.dt,
            y (S.θ (Q.γ d) l) ((t - S.t₀ (Q.γ d)) / S.dt)] (Q.P d)|
        ≤ N p K ^ (-r) * (N p K ^ ε₂ * N p K ^ (-L q)) := mul_le_mul_of_nonneg_left hfx hNr.le
      _ = N p K ^ ε₂ * (N p K ^ (-r) * N p K ^ (-L q)) := by ring
      _ = N p K ^ ε₂ * N p K ^ (-L p) := by
          rw [← Real.rpow_add hN0, hLq, show -r + -(L p - r) = -L p by ring]
      _ ≤ N p K ^ ε₃ * N p K ^ (-L p) :=
          mul_le_mul_of_nonneg_right hεle (Real.rpow_nonneg hN0.le _)

end RefStep

end Submission.Obl.k4_scalar_true_terminal_lifting
