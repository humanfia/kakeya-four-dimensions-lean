import Submission.Obl.k4_scalar_initial_true_horizon.InitialParams

/-!
# The fixed complexity exponent and the per-sample budgets

`B = M + D + 2⌈κ⌉ + 3⌈L⌉ + 2⌈|f(L)|⌉ + 10` absorbs the event format, the inverse chart
widths `2^kmax 2^T`, the chart count `W / (Φf q / 2^kmax)` and all parameter sizes; the
time budget `2^T ≤ N^(L + ε)` and the slack budget `4K + 3 ≤ N^ε` hold eventually.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The fixed complexity exponent of the initial atlas. -/
noncomputable def Bpar (p : Data) : ℕ :=
  M p + D p + 2 * ⌈kappaPar p⌉₊ + 3 * ⌈L p⌉₊ + 2 * ⌈|profile p (L p)|⌉₊ + 10

theorem Bpar_ge_one (p : Data) : 1 ≤ Bpar p := by unfold Bpar; omega

theorem M_le_Bpar (p : Data) : M p ≤ Bpar p := by unfold Bpar; omega

theorem D_le_Bpar (p : Data) : D p ≤ Bpar p := by unfold Bpar; omega

section budgets

variable {p : Data} (hp : Exact p)
include hp

/-- `N^a ≤ N^B` whenever `a ≤ B`. -/
theorem rpow_le_Bpar (k : ℕ) {a : ℝ} (ha : a ≤ (Bpar p : ℝ)) : N p k ^ a ≤ N p k ^ (Bpar p : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le (hp.N_one_le k) ha

/-- `C N^a ≤ N^(a + b)` when `C ≤ 2^b`. -/
theorem const_mul_rpow_le (k : ℕ) {a b C : ℝ} (hb : 0 ≤ b) (hC : C ≤ 2 ^ b) :
    C * N p k ^ a ≤ N p k ^ (a + b) := by
  have hN := hp.N_pos k
  rw [Real.rpow_add hN, mul_comm (N p k ^ a)]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
  exact hC.trans (Real.rpow_le_rpow (by norm_num) (hp.resolution_ge k) hb)

theorem format_budget (k : ℕ) : N p k ^ (M p : ℝ) + 18 ≤ N p k ^ (Bpar p : ℝ) := by
  have hN := hp.N_pos k
  have h1 : (1 : ℝ) ≤ N p k ^ (M p : ℝ) := Real.one_le_rpow (hp.N_one_le k) (Nat.cast_nonneg _)
  have h2 : 19 * N p k ^ (M p : ℝ) ≤ N p k ^ ((M p : ℝ) + 5) :=
    const_mul_rpow_le hp k (by norm_num) (by norm_num)
  have h3 : N p k ^ ((M p : ℝ) + 5) ≤ N p k ^ (Bpar p : ℝ) := by
    apply rpow_le_Bpar hp k
    have : M p + 5 ≤ Bpar p := by unfold Bpar; omega
    exact_mod_cast this
  linarith

theorem kappa_le_ceil : kappaPar p ≤ (⌈kappaPar p⌉₊ : ℝ) := Nat.le_ceil _

/-- Inverse chart widths: `2^kmax 2^T ≤ N^B`. -/
theorem inverse_width_budget (k : ℕ) :
    (2 : ℝ) ^ kmaxPar p k * 2 ^ Tpar p k ≤ N p k ^ (Bpar p : ℝ) := by
  have hN := hp.N_pos k
  have h1 := two_pow_kmax_le hp k
  have h2 := two_pow_Tpar_le hp k
  have hstep : (2 : ℝ) ^ kmaxPar p k * 2 ^ Tpar p k ≤ 4 * N p k ^ (kappaPar p + L p) := by
    rw [Real.rpow_add hN]
    calc (2 : ℝ) ^ kmaxPar p k * 2 ^ Tpar p k ≤ (2 * N p k ^ kappaPar p) * (2 * N p k ^ L p) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 * (N p k ^ kappaPar p * N p k ^ L p) := by ring
  refine hstep.trans ((const_mul_rpow_le hp k (b := 2) (by norm_num) (by norm_num)).trans ?_)
  apply rpow_le_Bpar hp k
  have hk := kappa_le_ceil hp
  have hL : L p ≤ (⌈L p⌉₊ : ℝ) := Nat.le_ceil _
  have : (⌈kappaPar p⌉₊ : ℝ) + ⌈L p⌉₊ + 2 ≤ Bpar p := by
    unfold Bpar; push_cast
    have h0 : (0 : ℝ) ≤ ⌈kappaPar p⌉₊ := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ ⌈L p⌉₊ := Nat.cast_nonneg _
    have h0'' : (0 : ℝ) ≤ ⌈|profile p (L p)|⌉₊ := Nat.cast_nonneg _
    have h0m : (0 : ℝ) ≤ M p := Nat.cast_nonneg _
    have h0d : (0 : ℝ) ≤ D p := Nat.cast_nonneg _
    linarith
  linarith

/-- The chart count: `W / (Φf q / 2^kmax) ≤ N^B` for every loss `ε ≤ 1`. -/
theorem count_budget (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (worlds p k : ℝ) / (floorPar p k ε * (qPar p k / 2 ^ kmaxPar p k)) ≤
      N p k ^ (Bpar p : ℝ) := by
  have hN := hp.N_pos k
  have hN1 := hp.N_one_le k
  have hq := qPar_pos hp k
  set Φ := profile p (L p) with hΦ
  have hW : (worlds p k : ℝ) ≤ N p k ^ (M p : ℝ) := (hp.2.1 k).1
  have hqinv : qPar p k * 2 ^ Tpar p k = 1 := qPar_mul_two_pow hp k
  have hfl : floorPar p k ε * (qPar p k / 2 ^ kmaxPar p k) =
      N p k ^ (-Φ) * N p k ^ (-ε) / ((2 : ℝ) ^ kmaxPar p k * (2 ^ Tpar p k) ^ 2) := by
    unfold floorPar
    have h2T : (2 : ℝ) ^ Tpar p k ≠ 0 := by positivity
    have hq' : qPar p k = 1 / 2 ^ Tpar p k := rfl
    rw [hq', hΦ]
    field_simp
  rw [hfl, div_div_eq_mul_div]
  have hden : 0 < N p k ^ (-Φ) * N p k ^ (-ε) := by positivity
  rw [div_le_iff₀ hden]
  -- `W 2^kmax 4^T ≤ 8 N^(M + κ + 2L)` and `N^(-Φ) N^(-ε) ≥ N^(-|Φ| - 1)`
  have h1 := two_pow_kmax_le hp k
  have h2 := two_pow_Tpar_le hp k
  have hnum : (worlds p k : ℝ) * ((2 : ℝ) ^ kmaxPar p k * (2 ^ Tpar p k) ^ 2) ≤
      8 * N p k ^ ((M p : ℝ) + kappaPar p + 2 * L p) := by
    have hsq : ((2 : ℝ) ^ Tpar p k) ^ 2 ≤ (2 * N p k ^ L p) ^ 2 := by gcongr
    calc (worlds p k : ℝ) * ((2 : ℝ) ^ kmaxPar p k * (2 ^ Tpar p k) ^ 2)
        ≤ N p k ^ (M p : ℝ) * ((2 * N p k ^ kappaPar p) * (2 * N p k ^ L p) ^ 2) := by
          gcongr
      _ = 8 * (N p k ^ (M p : ℝ) * N p k ^ kappaPar p * (N p k ^ L p) ^ 2) := by ring
      _ = 8 * N p k ^ ((M p : ℝ) + kappaPar p + 2 * L p) := by
          rw [Real.rpow_add hN, Real.rpow_add hN, ← Real.rpow_natCast (N p k ^ L p),
            ← Real.rpow_mul hN.le]
          push_cast; ring_nf
  have hlow : N p k ^ (-|Φ| - 1) ≤ N p k ^ (-Φ) * N p k ^ (-ε) := by
    rw [← Real.rpow_add hN]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self Φ])
  have htarget : 8 * N p k ^ ((M p : ℝ) + kappaPar p + 2 * L p) ≤
      N p k ^ (Bpar p : ℝ) * N p k ^ (-|Φ| - 1) := by
    rw [← Real.rpow_add hN]
    refine (const_mul_rpow_le hp k (b := 3) (by norm_num) (by norm_num)).trans ?_
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hk := kappa_le_ceil hp
    have hL : L p ≤ (⌈L p⌉₊ : ℝ) := Nat.le_ceil _
    have hP : |Φ| ≤ (⌈|Φ|⌉₊ : ℝ) := Nat.le_ceil _
    unfold Bpar; push_cast
    have h0 : (0 : ℝ) ≤ ⌈kappaPar p⌉₊ := Nat.cast_nonneg _
    have h0' : (0 : ℝ) ≤ ⌈L p⌉₊ := Nat.cast_nonneg _
    have h0d : (0 : ℝ) ≤ D p := Nat.cast_nonneg _
    have hLpos := hp.length_pos
    linarith
  calc (worlds p k : ℝ) * ((2 : ℝ) ^ kmaxPar p k * (2 ^ Tpar p k) ^ 2)
      ≤ 8 * N p k ^ ((M p : ℝ) + kappaPar p + 2 * L p) := hnum
    _ ≤ N p k ^ (Bpar p : ℝ) * N p k ^ (-|Φ| - 1) := htarget
    _ ≤ N p k ^ (Bpar p : ℝ) * (N p k ^ (-Φ) * N p k ^ (-ε)) :=
        mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg hN.le _)

/-- Parameter sizes: `4K + 3 ≤ N^B` eventually. -/
theorem eventually_param_budget :
    ∀ᶠ k in atTop, 4 * K p k + 3 ≤ N p k ^ (Bpar p : ℝ) := by
  filter_upwards [hp.slack_subpower 1 (by norm_num)] with k hK
  have hN := hp.N_pos k
  rw [Real.rpow_one] at hK
  have h1 : 7 * N p k ^ (1 : ℝ) ≤ N p k ^ ((1 : ℝ) + 3) :=
    const_mul_rpow_le hp k (by norm_num) (by norm_num)
  rw [Real.rpow_one] at h1
  have h2 : N p k ^ ((1 : ℝ) + 3) ≤ N p k ^ (Bpar p : ℝ) := by
    apply rpow_le_Bpar hp k
    have : 4 ≤ Bpar p := by unfold Bpar; omega
    norm_num; exact_mod_cast this
  have hN1 := hp.N_one_le k
  linarith

/-- Slack: `4K + 3 ≤ N^ε` eventually. -/
theorem eventually_slack_budget {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, 4 * K p k + 3 ≤ N p k ^ ε := by
  filter_upwards [hp.slack_subpower (ε / 2) (by positivity),
    eventually_const_le_rpow hp.resolution_tendsto (a := ε / 2) (by positivity) 7] with k hK h7
  have hN := hp.N_pos k
  have hsplit : N p k ^ ε = N p k ^ (ε / 2) * N p k ^ (ε / 2) := by
    rw [← Real.rpow_add hN]; ring_nf
  have hK1 := hp.slack_ge k
  rw [hsplit]
  nlinarith

/-- Time: `2^T ≤ N^(L + ε)` eventually. -/
theorem eventually_time_budget {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, (2 : ℝ) ^ Tpar p k ≤ N p k ^ (L p + ε) := by
  filter_upwards [eventually_const_le_rpow hp.resolution_tendsto hε 2] with k h2
  have hN := hp.N_pos k
  calc (2 : ℝ) ^ Tpar p k ≤ 2 * N p k ^ L p := two_pow_Tpar_le hp k
    _ ≤ N p k ^ ε * N p k ^ L p := by gcongr
    _ = N p k ^ (L p + ε) := by rw [← Real.rpow_add hN, add_comm]

end budgets

end Submission.Obl.k4_scalar_initial_true_horizon
