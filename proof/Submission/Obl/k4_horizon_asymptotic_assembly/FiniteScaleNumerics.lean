/- Adapted from this LOT tree, obligation o103, session x0354, commit162b3a6,
Submission/Obl/k4_initial_horizon_bound/FiniteScaleNumerics.lean.
Named forms and Boolean calculus originally came from o103/x0360, commits642b39c andb0c6023;
the finite interface definitions came from o160/x0559/b0539eb, as attributed below. -/

import Submission.Obl.k4_horizon_asymptotic_assembly.InitialParameters

/-! Numerical choices for the finite weighted atlas interface. The true-floor
constraint can be imposed exactly, without putting analytic constants in the
raw complexity budget. -/

namespace Submission.Obl.k4_horizon_asymptotic_assembly

noncomputable def initialFloor (n R q κ : ℝ) : ℝ := 4 * n * (R * q) ^ 2 / κ

theorem initialFloor_pos {n R q κ : ℝ} (hn : 0 < n) (hR : 0 < R)
    (hq : 0 < q) (hκ : 0 < κ) : 0 < initialFloor n R q κ := by
  unfold initialFloor
  positivity

theorem initialFloor_constraint {n R q κ : ℝ} (hκ : κ ≠ 0) :
    4 * n * (R * q) ^ 2 = initialFloor n R q κ * κ := by
  unfold initialFloor
  exact (div_mul_cancel₀ _ hκ).symm

/-- With the exact floor choice, every physical scale and the native density
exponent cancel from the relative support-table error. -/
theorem initial_relative_error_eq {C K n q κ N D ζ τ : ℝ}
    (hn : n ≠ 0) (hq : q ≠ 0) (hκ : κ ≠ 0) (hK : K ≠ 0)
    (hN : 0 < N) :
    C * K ^ 3 * initialFloor n (2 * K + 2) q κ * D ^ ζ /
        ((16 * K)⁻¹ * (n * N ^ (-τ)) * q ^ 2) =
      64 * C * K ^ 4 * (2 * K + 2) ^ 2 * N ^ τ * D ^ ζ / κ := by
  rw [Real.rpow_neg hN.le]
  unfold initialFloor
  field_simp
  <;> ring

/-- A fixed polynomial envelope for the whole raw complexity budget.
The slack exponent is only used through `κ ≤ N`. -/
theorem initial_raw_budget_power {N H K D Jt n R q κ : ℝ}
    {MH MD MP MF : ℕ} (hN : 2 ≤ N) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hn : 0 < n) (hR : 1 ≤ R) (hq : 0 < q) (hκ : 0 < κ)
    (hHbound : H ≤ N ^ MH) (hKbound : K ≤ N ^ MH)
    (hDbound : D ≤ N ^ MD) (hJbound : Jt ≤ N ^ MP)
    (hninv : n⁻¹ ≤ N ^ MF) (hqinv : q⁻¹ ≤ N ^ MP) (hκN : κ ≤ N) :
    1 + H + K + D + Jt + (initialFloor n R q κ)⁻¹ ≤
      N ^ (MH + MD + MF + 2 * MP + 4) := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  let E := MH + MD + MF + 2 * MP + 1
  have hp {a : ℕ} (ha : a ≤ E) : N ^ a ≤ N ^ E := pow_le_pow_right₀ hN1 ha
  have h1 : (1 : ℝ) ≤ N ^ E := one_le_pow₀ hN1
  have hHb : H ≤ N ^ E := hHbound.trans (hp (by dsimp [E]; omega))
  have hKb : K ≤ N ^ E := hKbound.trans (hp (by dsimp [E]; omega))
  have hDb : D ≤ N ^ E := hDbound.trans (hp (by dsimp [E]; omega))
  have hJb : Jt ≤ N ^ E := hJbound.trans (hp (by dsimp [E]; omega))
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hinv : (initialFloor n R q κ)⁻¹ ≤ κ * n⁻¹ * (q⁻¹) ^ 2 := by
    have heq : (initialFloor n R q κ)⁻¹ =
        (κ * n⁻¹ * (q⁻¹) ^ 2) / (4 * R ^ 2) := by
      unfold initialFloor
      field_simp
      <;> ring
    rw [heq]
    apply div_le_self (by positivity)
    nlinarith [sq_nonneg (R - 1)]
  have hinvN : (initialFloor n R q κ)⁻¹ ≤ N ^ (1 + MF + 2 * MP) := by
    calc
      _ ≤ κ * n⁻¹ * (q⁻¹) ^ 2 := hinv
      _ ≤ N * N ^ MF * (N ^ MP) ^ 2 := by gcongr
      _ = N ^ (1 + MF + 2 * MP) := by
        simp only [pow_add, pow_mul, pow_one]
        ring
  have hinvb : (initialFloor n R q κ)⁻¹ ≤ N ^ E :=
    hinvN.trans (hp (by dsimp [E]; omega))
  have h8 : (6 : ℝ) ≤ N ^ 3 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
    norm_num at hpow ⊢
    linarith
  calc
    _ ≤ 6 * N ^ E := by linarith
    _ ≤ N ^ E * N ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h8 (by positivity : 0 ≤ N ^ E)]
    _ = N ^ (MH + MD + MF + 2 * MP + 4) := by
      rw [← pow_add]

/-- A fixed upper mesh exponent pays for the plank loss. The returned
constant and native subpower factors affect only how late the sample is. -/
theorem eventually_initial_relative_error_small {N K D : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Filter.Tendsto N Filter.atTop Filter.atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)
    {J ε : ℝ} (hJ : 0 < J) (hε : 0 < ε) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ᶠ k in Filter.atTop, 0 ≤ D k ∧ D k ≤ N k ^ (2 * J)) :
    ∀ᶠ k in Filter.atTop,
      64 * C * K k ^ 4 * (2 * K k + 2) ^ 2 *
        N k ^ (ε / 8) * D k ^ (ε / (16 * J)) / N k ^ ε ≤ 1 / 4 := by
  have hs := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hK hsub 6 (show -3 * ε / 4 < 0 by linarith)
    (show (0 : ℝ) ≤ 4096 * C by positivity)
  filter_upwards [hs, hD] with k hk hmesh
  have hNk : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKk : 0 ≤ K k := (zero_le_one.trans (hK k))
  have hrad : (2 * K k + 2) ^ 2 ≤ 16 * K k ^ 2 := by
    nlinarith [sq_nonneg (K k - 1), hK k]
  have hpow : D k ^ (ε / (16 * J)) ≤ N k ^ (ε / 8) := by
    calc
      _ ≤ (N k ^ (2 * J)) ^ (ε / (16 * J)) :=
        Real.rpow_le_rpow hmesh.1 hmesh.2 (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul hNk.le]
        congr 1
        field_simp
        <;> ring
  have hratio : N k ^ (ε / 8) * N k ^ (ε / 8) / N k ^ ε =
      N k ^ (-3 * ε / 4) := by
    rw [← Real.rpow_add hNk, ← Real.rpow_sub hNk]
    congr 1
    ring
  have hb : 64 * C * K k ^ 4 * (2 * K k + 2) ^ 2 *
      N k ^ (ε / 8) * D k ^ (ε / (16 * J)) / N k ^ ε ≤
      1024 * C * K k ^ 6 * N k ^ (-3 * ε / 4) := by
    calc
      _ ≤ 64 * C * K k ^ 4 * (16 * K k ^ 2) *
          N k ^ (ε / 8) * N k ^ (ε / 8) / N k ^ ε := by
        gcongr
        exact Real.rpow_nonneg hmesh.1 _
      _ = _ := by rw [← hratio]; ring
  simp only [Real.rpow_zero] at hk
  nlinarith

end Submission.Obl.k4_horizon_asymptotic_assembly
