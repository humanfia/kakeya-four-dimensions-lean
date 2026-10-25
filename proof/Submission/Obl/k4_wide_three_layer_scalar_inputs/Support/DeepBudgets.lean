import Submission.Obl.k4_wide_three_layer_scalar_inputs.Model
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Sigma
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.PolyLip
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.GeometricOutput
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Set MeasureTheory Filter

noncomputable section

/-- These are exactly the four right sides of `deep_coord_variation`. -/
def deepCoordinateBudgets (q g a qe ge ae K : ℝ) : Fin 4 → ℝ :=
  let W := 14 * K ^ 2 * qe ^ 2 + 2 * K * qe * ge
  ![qe / q, 5 * K * qe / q,
    (10 * K ^ 2 * qe + 2 * K * qe * ge) / (q * g),
    (K * (1 + ae / qe) * (5 * K * qe) + K * (1 + ae / qe ^ 2) * W + 2 * K * ae +
      K * (1 + a / q) * (5 * K * qe) + K * (1 + a / q ^ 2) * W) / a]

/-- A uniform scalar bound for all four original deep-block variations. The inverse
coarse width is bounded by `P`, which later equals `N^s`. -/
theorem deepCoordinateBudgets_bound {q g a qe ge ae K P : ℝ}
    (hK : 1 ≤ K) (hP : 1 ≤ P) (hq : 0 < q) (hg : 0 < g) (ha : 0 < a)
    (hqe : 0 < qe) (hge : 0 ≤ ge) (hge₁ : ge ≤ 1) (hae : 0 ≤ ae) (haege : ae ≤ ge)
    (haP : a * P = 1) (hqinv : q⁻¹ ≤ K * P) (hginv : g⁻¹ ≤ P)
    (hqege : qe ≤ K * ge) (hgeqe : ge / qe ≤ K) :
    ∀ e, deepCoordinateBudgets q g a qe ge ae K e ≤ 100 * K ^ 7 * P ^ 2 * ge := by
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  have hpow (m n : ℕ) (hmn : m ≤ n) : K ^ m ≤ K ^ n := pow_le_pow_right₀ hK hmn
  have hP₂ : P ≤ P ^ 2 := by nlinarith
  have hsqge : ge ^ 2 ≤ ge := by nlinarith
  have ha_inv : a⁻¹ = P := by
    apply (mul_left_cancel₀ ha.ne')
    rw [mul_inv_cancel₀ ha.ne', haP]
  have haq : a / q ≤ K := by
    calc
      _ = a * q⁻¹ := div_eq_mul_inv _ _
      _ ≤ a * (K * P) := mul_le_mul_of_nonneg_left hqinv ha.le
      _ = K * (a * P) := by ring
      _ = K := by rw [haP, mul_one]
  have haq₂ : a / q ^ 2 ≤ K ^ 2 * P := by
    calc
      _ = a * (q⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ a * (K * P) ^ 2 := by gcongr
      _ = K ^ 2 * P * (a * P) := by ring
      _ = K ^ 2 * P := by rw [haP, mul_one]
  let W := 14 * K ^ 2 * qe ^ 2 + 2 * K * qe * ge
  have hW₀ : 0 ≤ W := by dsimp [W]; positivity
  have hW : W ≤ 16 * K ^ 4 * ge ^ 2 := by
    calc
      _ ≤ 14 * K ^ 2 * (K * ge) ^ 2 + 2 * K * (K * ge) * ge := by dsimp [W]; gcongr
      _ = (14 * K ^ 4 + 2 * K ^ 2) * ge ^ 2 := by ring
      _ ≤ 16 * K ^ 4 * ge ^ 2 := by gcongr; linarith [hpow 2 4 (by omega)]
  have hWqe : W / qe ^ 2 ≤ 16 * K ^ 2 := by
    have heq : W / qe ^ 2 = 14 * K ^ 2 + 2 * K * (ge / qe) := by
      dsimp [W]
      field_simp
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hgeqe (show 0 ≤ 2 * K by positivity)
    nlinarith
  let B := K ^ 7 * P * ge
  have hB₀ : 0 ≤ B := by dsimp [B]; positivity
  have hcommon (j : ℕ) (hj : j ≤ 7) : K ^ j * ge ≤ B := by
    calc
      _ ≤ K ^ 7 * ge := mul_le_mul_of_nonneg_right (hpow j 7 hj) hge
      _ ≤ K ^ 7 * P * ge := by
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (pow_nonneg hK₀ _) hP) hge
  have hterm₁ : K * (1 + ae / qe) * (5 * K * qe) ≤ 10 * B := by
    have heq : K * (1 + ae / qe) * (5 * K * qe) = 5 * K ^ 2 * (qe + ae) := by
      field_simp
    rw [heq]
    calc
      _ ≤ 5 * K ^ 2 * (K * ge + ge) := by gcongr
      _ ≤ 10 * (K ^ 3 * ge) := by nlinarith [mul_le_mul_of_nonneg_right hK hge]
      _ ≤ 10 * B := by gcongr; exact hcommon 3 (by omega)
  have hterm₂ : K * (1 + ae / qe ^ 2) * W ≤ 32 * B := by
    have heq : K * (1 + ae / qe ^ 2) * W = K * W + K * ae * (W / qe ^ 2) := by ring
    rw [heq]
    calc
      _ ≤ K * (16 * K ^ 4 * ge ^ 2) + K * ge * (16 * K ^ 2) := by gcongr
      _ = 16 * (K ^ 5 * ge ^ 2) + 16 * (K ^ 3 * ge) := by ring
      _ ≤ 16 * (K ^ 5 * ge) + 16 * (K ^ 3 * ge) := by gcongr
      _ ≤ 32 * B := by linarith [hcommon 5 (by omega), hcommon 3 (by omega)]
  have hterm₃ : 2 * K * ae ≤ 2 * B := by
    calc
      _ ≤ 2 * (K ^ 1 * ge) := by simpa only [pow_one, ← mul_assoc] using mul_le_mul_of_nonneg_left haege (show 0 ≤ 2 * K by positivity)
      _ ≤ 2 * B := by gcongr; exact hcommon 1 (by omega)
  have hterm₄ : K * (1 + a / q) * (5 * K * qe) ≤ 10 * B := by
    calc
      _ ≤ K * (2 * K) * (5 * K * (K * ge)) := by gcongr; linarith
      _ = 10 * (K ^ 4 * ge) := by ring
      _ ≤ 10 * B := by gcongr; exact hcommon 4 (by omega)
  have hterm₅ : K * (1 + a / q ^ 2) * W ≤ 32 * B := by
    have hKP : 1 ≤ K ^ 2 * P := by nlinarith [hpow 0 2 (by omega)]
    calc
      _ ≤ K * (2 * K ^ 2 * P) * (16 * K ^ 4 * ge ^ 2) := by gcongr; linarith
      _ = 32 * (K ^ 7 * P * ge ^ 2) := by ring
      _ ≤ 32 * (K ^ 7 * P * ge) := by gcongr
      _ = 32 * B := rfl
  have hres : (K * (1 + ae / qe) * (5 * K * qe) + K * (1 + ae / qe ^ 2) * W + 2 * K * ae +
      K * (1 + a / q) * (5 * K * qe) + K * (1 + a / q ^ 2) * W) / a ≤
      100 * K ^ 7 * P ^ 2 * ge := by
    rw [div_eq_mul_inv, ha_inv]
    calc
      _ ≤ (86 * B) * P := by gcongr; linarith
      _ = 86 * (K ^ 7 * P ^ 2 * ge) := by dsimp [B]; ring
      _ ≤ 100 * (K ^ 7 * P ^ 2 * ge) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = _ := by ring
  have hbase : 5 * K * qe / q ≤ 5 * K ^ 3 * P * ge := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 5 * K * (K * ge) * (K * P) := by gcongr
      _ = _ := by ring
  have htime : qe / q ≤ K ^ 2 * P * ge := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (K * ge) * (K * P) := by gcongr
      _ = _ := by ring
  have htrans : (10 * K ^ 2 * qe + 2 * K * qe * ge) / (q * g) ≤
      12 * K ^ 4 * P ^ 2 * ge := by
    have hnum : 10 * K ^ 2 * qe + 2 * K * qe * ge ≤ 12 * K ^ 3 * ge := by
      calc
        _ ≤ 10 * K ^ 2 * (K * ge) + 2 * K * (K * ge) * 1 := by gcongr
        _ ≤ 12 * K ^ 3 * ge := by nlinarith only [mul_le_mul_of_nonneg_right (hpow 2 3 (by omega)) hge]
    rw [div_eq_mul_inv, mul_inv]
    calc
      _ ≤ (12 * K ^ 3 * ge) * ((K * P) * P) := by gcongr
      _ = _ := by ring
  intro e
  fin_cases e
  · exact htime.trans (by
      gcongr
      · exact (hpow 2 7 (by omega)).trans (by nlinarith only [pow_nonneg hK₀ 7])
      )
  · exact hbase.trans (by gcongr <;> norm_num)
  · exact htrans.trans (by gcongr <;> norm_num)
  · exact hres

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original dyadic atlas scale bounds supply every scalar hypothesis in the
deep-variation bound. No lower bound on the horizontal rate beyond positivity is used. -/
theorem deepCoordinateBudgets_native_bound (hv : cfg.Valid) {k : ℕ} {s se R : ℝ}
    (hs : 0 ≤ s) (hse : 0 ≤ se) (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R) :
    ∀ e, deepCoordinateBudgets (((2 : ℝ) ^ cfg.T k s)⁻¹) (cfg.N k ^ (-cfg.κ * s))
      (cfg.N k ^ (-s)) (((2 : ℝ) ^ cfg.T k se)⁻¹) (cfg.N k ^ (-cfg.κ * se))
      (cfg.N k ^ (-se)) (cfg.K k) e ≤
        100 * (cfg.K k) ^ 7 * cfg.N k ^ (2 * s - cfg.κ * se) := by
  have hN : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hN₀ : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hK : 1 ≤ cfg.K k := hv.subpower.1 k
  have hK₀ : 0 < cfg.K k := zero_lt_one.trans_le hK
  have htime : cfg.N k ^ (cfg.κ * s) ≤ cfg.N k ^ s :=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [hv.rate_le_one])
  have hcancel (z : ℝ) : cfg.N k ^ (-cfg.κ * z) * cfg.N k ^ (cfg.κ * z) = 1 := by
    rw [← Real.rpow_add hN₀, show -cfg.κ * z + cfg.κ * z = 0 by ring, Real.rpow_zero]
  have haq : cfg.N k ^ (-s) * cfg.N k ^ s = 1 := by
    rw [← Real.rpow_add hN₀, neg_add_cancel, Real.rpow_zero]
  have hqinv : ((((2 : ℝ) ^ cfg.T k s)⁻¹)⁻¹) ≤ cfg.K k * cfg.N k ^ s := by
    rw [inv_inv]
    exact hB.T_hi.trans (mul_le_mul_of_nonneg_left htime hK₀.le)
  have hginv : (cfg.N k ^ (-cfg.κ * s))⁻¹ ≤ cfg.N k ^ s := by
    rw [← Real.rpow_neg hN₀.le]
    simpa only [neg_mul, neg_neg] using htime
  have hqe : 0 < ((2 : ℝ) ^ cfg.T k se)⁻¹ := by positivity
  have hqege : ((2 : ℝ) ^ cfg.T k se)⁻¹ ≤ cfg.K k * cfg.N k ^ (-cfg.κ * se) := by
    have hh := inv_anti₀ (div_pos (Real.rpow_pos_of_pos hN₀ _) hK₀) hBe.T_lo
    calc
      _ ≤ (cfg.N k ^ (cfg.κ * se) / cfg.K k)⁻¹ := hh
      _ = cfg.K k * cfg.N k ^ (-cfg.κ * se) := by
        rw [inv_div, div_eq_mul_inv, ← Real.rpow_neg hN₀.le]
        congr 2
        ring
  have hgeqe : cfg.N k ^ (-cfg.κ * se) / ((2 : ℝ) ^ cfg.T k se)⁻¹ ≤ cfg.K k := by
    rw [div_eq_mul_inv, inv_inv]
    calc
      _ ≤ cfg.N k ^ (-cfg.κ * se) * (cfg.K k * cfg.N k ^ (cfg.κ * se)) := by gcongr; exact hBe.T_hi
      _ = cfg.K k * (cfg.N k ^ (-cfg.κ * se) * cfg.N k ^ (cfg.κ * se)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  have hb := deepCoordinateBudgets_bound
    (q := ((2 : ℝ) ^ cfg.T k s)⁻¹) (g := cfg.N k ^ (-cfg.κ * s))
    (a := cfg.N k ^ (-s)) (qe := ((2 : ℝ) ^ cfg.T k se)⁻¹)
    (ge := cfg.N k ^ (-cfg.κ * se)) (ae := cfg.N k ^ (-se)) (P := cfg.N k ^ s)
    hK (Real.one_le_rpow hN hs)
    (show (0 : ℝ) < ((2 : ℝ) ^ cfg.T k s)⁻¹ by positivity)
    (Real.rpow_pos_of_pos hN₀ _) (Real.rpow_pos_of_pos hN₀ _) hqe
    (Real.rpow_pos_of_pos hN₀ _).le
    (Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith [hv.rate_pos]))
    (Real.rpow_pos_of_pos hN₀ _).le
    (Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [hv.rate_le_one]))
    haq hqinv hginv hqege hgeqe
  have heq : (cfg.N k ^ s) ^ 2 * cfg.N k ^ (-cfg.κ * se) =
      cfg.N k ^ (2 * s - cfg.κ * se) := by
    rw [← Real.rpow_natCast (cfg.N k ^ s) 2, ← Real.rpow_mul hN₀.le, ← Real.rpow_add hN₀]
    congr 1
    ring
  intro e
  calc
    _ ≤ 100 * (cfg.K k) ^ 7 * ((cfg.N k ^ s) ^ 2 * cfg.N k ^ (-cfg.κ * se)) := by
      simpa only [mul_assoc] using hb e
    _ = _ := by rw [heq]

/-- Any fixed strict exponent margin pays the four numerical hypotheses of
`sigma_prune`, uniformly over the original atlas at the chosen two depths. -/
theorem eventually_deepCoordinateBudgets (hv : cfg.Valid) {s se η z : ℝ}
    (hs : 0 ≤ s) (hse : 0 ≤ se) (hη : 0 < η)
    (hmargin : 7 * η + 2 * s - cfg.κ * se < -z) :
    ∀ᶠ k in atTop, ∀ R : ℝ, BlocksAt cfg k s R → BlocksAt cfg k se R →
      ∀ e, deepCoordinateBudgets (((2 : ℝ) ^ cfg.T k s)⁻¹) (cfg.N k ^ (-cfg.κ * s))
        (cfg.N k ^ (-s)) (((2 : ℝ) ^ cfg.T k se)⁻¹) (cfg.N k ^ (-cfg.κ * se))
        (cfg.N k ^ (-se)) (cfg.K k) e ≤ cfg.N k ^ (-z) := by
  filter_upwards [hv.subpower.2 η hη, hv.scale_limit.eventually
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 100 hmargin)]
    with k hKN hbudget
  intro R hB hBe e
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  calc
    _ ≤ 100 * (cfg.K k) ^ 7 * cfg.N k ^ (2 * s - cfg.κ * se) :=
      deepCoordinateBudgets_native_bound hv hs hse hB hBe e
    _ ≤ 100 * (cfg.N k ^ η) ^ 7 * cfg.N k ^ (2 * s - cfg.κ * se) := by
      gcongr
      exact (zero_le_one.trans (hv.subpower.1 k))
    _ = 100 * cfg.N k ^ (7 * η + 2 * s - cfg.κ * se) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, mul_assoc, ← Real.rpow_add hN]
      congr 2
      ring
    _ ≤ _ := hbudget

/-- A bounded common field preserves a small coordinate variation on the original
block. The estimate is independent of the magnitude of the uncorrected residual. -/
theorem corrected_residual_variation_bound {C : Fin 4 → ℝ} {H K D x y U X x' y' U' X' : ℝ}
    (hH : 1 ≤ H) (hK : 1 ≤ K) (hC : ∀ e, |C e| ≤ H)
    (hx : |x| ≤ 1) (hx' : |x'| ≤ 1) (hy : |y| ≤ K) (hy' : |y'| ≤ K)
    (hU : |U| ≤ K) (hU' : |U'| ≤ K)
    (hvarx : |x - x'| ≤ D) (hvary : |y - y'| ≤ D) (hvarU : |U - U'| ≤ D)
    (hvarX : |X - X'| ≤ D) :
    |(X - transv C x y U) - (X' - transv C x' y' U')| ≤ 16 * H * K * D := by
  have hH₀ : 0 ≤ H := zero_le_one.trans hH
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hD : 0 ≤ D := (abs_nonneg _).trans hvarx
  have hp := predQ_diff (p := fun _ => 0) (τ := C) (H := H) (X := 1) (Y := K) (Ub := K)
    (fun _ => by simpa using hH₀) hC hx hx' hy hy' hU hU'
  simp only [predQ, quadZ, zero_mul, zero_add, add_zero] at hp
  have hpoly : |transv C x y U - transv C x' y' U'| ≤ 15 * H * K * D := by
    calc
      _ ≤ H * ((1 + 2 * 1 + K + K) * |x - x'| + (1 + 1 + 2 * K + K) * |y - y'| +
          (1 + 1 + K + 2 * K) * |U - U'|) := hp
      _ ≤ H * ((1 + 2 * 1 + K + K) * D + (1 + 1 + 2 * K + K) * D +
          (1 + 1 + K + 2 * K) * D) := by gcongr
      _ = H * (7 + 8 * K) * D := by ring
      _ ≤ H * (15 * K) * D := by gcongr; linarith
      _ = _ := by ring
  have hHK : 1 ≤ H * K := hH.trans (le_mul_of_one_le_right hH₀ hK)
  calc
    _ = |(X - X') - (transv C x y U - transv C x' y' U')| := by congr 1; ring
    _ ≤ |X - X'| + |transv C x y U - transv C x' y' U'| := abs_sub _ _
    _ ≤ D + 15 * H * K * D := add_le_add hvarX hpoly
    _ ≤ 16 * H * K * D := by nlinarith only [mul_le_mul_of_nonneg_right hHK hD]

/-- The scalar budget controls the actual four coordinates on every original deep
block meeting the original coarse block. -/
theorem deep_coord_variation_bound (hv : cfg.Valid) {k : ℕ} {s se R : ℝ}
    (hs : 0 ≤ s) (hse : 0 ≤ se) (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (hL : HorizontalForm (cfg.F k s i) L)
    (j : Fin (cfg.n k se)) {p p' : α × ℝ}
    (hp : p ∈ (cfg.B k se j ×ˢ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k se) (cfg.j k se j)) ∩ (cfg.B k s i ×ˢ
        Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i)))
    (hp' : p' ∈ (cfg.B k se j ×ˢ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k se) (cfg.j k se j)) ∩ (cfg.B k s i ×ˢ
        Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i))) :
    ∀ e, |coords (blockFrame cfg k s i L) (cfg.b k p.1) p.2 e -
      coords (blockFrame cfg k s i L) (cfg.b k p'.1) p'.2 e| ≤
        100 * (cfg.K k) ^ 7 * cfg.N k ^ (2 * s - cfg.κ * se) := by
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  let qe := ((2 : ℝ) ^ cfg.T k se)⁻¹
  let ge := cfg.N k ^ (-cfg.κ * se)
  let ae := cfg.N k ^ (-se)
  have hh := deep_coord_variation (hv.subpower.1 k) hN hB hBe i L hL j
    hp.1.1 hp'.1.1 hp.1.2 hp'.1.2 hp'.2.1 hp'.2.2 (blockFrame cfg k s i L) rfl
    qe ge ae (cfg.K k) (14 * (cfg.K k) ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge)
    rfl rfl rfl rfl rfl
  have hb := deepCoordinateBudgets_native_bound hv hs hse hB hBe
  intro e
  fin_cases e
  · exact hh.1.trans (hb 0)
  · exact hh.2.1.trans (hb 1)
  · exact hh.2.2.1.trans (hb 2)
  · exact hh.2.2.2.trans (hb 3)

/-- Corrected residuals inherit a fixed-power deep variation bound on the original
blocks, using only the original whole-block geometry. -/
theorem deep_corrected_variation_bound (hv : cfg.Valid) {k : ℕ} {s se R H : ℝ}
    (hs : 0 ≤ s) (hse : 0 ≤ se) (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (hL : HorizontalForm (cfg.F k s i) L)
    (C : Fin 4 → ℝ) (hH : 1 ≤ H) (hC : ∀ e, |C e| ≤ H)
    (j : Fin (cfg.n k se)) {p p' : α × ℝ}
    (hp : p ∈ (cfg.B k se j ×ˢ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k se) (cfg.j k se j)) ∩ (cfg.B k s i ×ˢ
        Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i)))
    (hp' : p' ∈ (cfg.B k se j ×ˢ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
      (cfg.T k se) (cfg.j k se j)) ∩ (cfg.B k s i ×ˢ
        Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i))) :
    let F := blockFrame cfg k s i L
    |(F.resid (cfg.b k p.1) p.2 - transv C (F.zt p.2) (F.zZ (cfg.b k p.1) p.2)
        (F.tr (cfg.b k p.1) p.2)) -
      (F.resid (cfg.b k p'.1) p'.2 - transv C (F.zt p'.2) (F.zZ (cfg.b k p'.1) p'.2)
        (F.tr (cfg.b k p'.1) p'.2))| ≤
        1600 * H * (cfg.K k) ^ 8 * cfg.N k ^ (2 * s - cfg.κ * se) := by
  have hN : 0 < cfg.N k := by linarith [hv.scale k]
  have hvar := deep_coord_variation_bound hv hs hse hB hBe i L hL j hp hp'
  have htime {t : ℝ}
      (ht : t ∈ Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i)) :
      |(blockFrame cfg k s i L).zt t| ≤ 1 := by
    rw [← blockFrame_interval i L] at ht
    have hq : 0 < (blockFrame cfg k s i L).q := by dsimp [blockFrame]; positivity
    unfold Frame.zt
    rw [abs_div, abs_of_pos hq, div_le_one hq]
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  have hgeom := whole_block_bounds hB hN i L hL hp.2.1
    (by rw [blockFrame_interval]; exact hp.2.2)
  have hgeom' := whole_block_bounds hB hN i L hL hp'.2.1
    (by rw [blockFrame_interval]; exact hp'.2.2)
  have hh := corrected_residual_variation_bound hH (hv.subpower.1 k) hC
    (htime hp.2.2) (htime hp'.2.2) hgeom.1 hgeom'.1 hgeom.2.1 hgeom'.2.1
    (hvar 0) (hvar 1) (hvar 2) (hvar 3)
  simp only [coords, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hh
  convert hh using 1 <;> ring

/-- A fixed strict margin also pays the corrected-residual variation required by
the final support pruning, for every admissible common field at once. -/
theorem eventually_deep_corrected_variation (hv : cfg.Valid) {s se η ε z : ℝ}
    (hs : 0 ≤ s) (hse : 0 ≤ se) (hη : 0 < η) (hε : 0 ≤ ε)
    (hmargin : ε + 8 * η + 2 * s - cfg.κ * se < -z) :
    ∀ᶠ k in atTop, ∀ R : ℝ, BlocksAt cfg k s R → BlocksAt cfg k se R →
      ∀ (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ), HorizontalForm (cfg.F k s i) L →
      ∀ C : Fin 4 → ℝ, (∀ e, |C e| ≤ cfg.N k ^ ε) →
      ∀ (j : Fin (cfg.n k se)) (p p' : α × ℝ),
      p ∈ (cfg.B k se j ×ˢ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
        (cfg.T k se) (cfg.j k se j)) ∩ (cfg.B k s i ×ˢ
          Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i)) →
      p' ∈ (cfg.B k se j ×ˢ Submission.Obl.k4_critical_conditional_row_preparation.Data.I
        (cfg.T k se) (cfg.j k se j)) ∩ (cfg.B k s i ×ˢ
          Submission.Obl.k4_critical_conditional_row_preparation.Data.I (cfg.T k s) (cfg.j k s i)) →
      let F := blockFrame cfg k s i L
      |(F.resid (cfg.b k p.1) p.2 - transv C (F.zt p.2) (F.zZ (cfg.b k p.1) p.2)
          (F.tr (cfg.b k p.1) p.2)) -
        (F.resid (cfg.b k p'.1) p'.2 - transv C (F.zt p'.2) (F.zZ (cfg.b k p'.1) p'.2)
          (F.tr (cfg.b k p'.1) p'.2))| ≤ cfg.N k ^ (-z) := by
  filter_upwards [hv.subpower.2 η hη, hv.scale_limit.eventually
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 1600 hmargin)]
    with k hKN hbudget
  intro R hB hBe i L hL C hC j p p' hp hp'
  have hN : 1 ≤ cfg.N k := by linarith [hv.scale k]
  have hN₀ : 0 < cfg.N k := zero_lt_one.trans_le hN
  calc
    _ ≤ 1600 * cfg.N k ^ ε * (cfg.K k) ^ 8 * cfg.N k ^ (2 * s - cfg.κ * se) :=
      deep_corrected_variation_bound hv hs hse hB hBe i L hL C (Real.one_le_rpow hN hε) hC j hp hp'
    _ ≤ 1600 * cfg.N k ^ ε * (cfg.N k ^ η) ^ 8 * cfg.N k ^ (2 * s - cfg.κ * se) := by
      gcongr
      exact (zero_le_one.trans (hv.subpower.1 k))
    _ = 1600 * cfg.N k ^ (ε + 8 * η + 2 * s - cfg.κ * se) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le, mul_assoc, ← Real.rpow_add hN₀,
        mul_assoc, ← Real.rpow_add hN₀]
      congr 2
      ring
    _ ≤ _ := hbudget

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
