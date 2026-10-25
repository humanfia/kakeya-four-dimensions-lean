import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.SourceBounds
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.PredictorCells
import Submission.Obl.k4_scalar_initial_true_horizon.Basic
import Submission.Lib.K4ContactNormalization.ResidualNormalization

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted

open MeasureTheory Set Filter MvPolynomial
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

noncomputable section

/-- The horizontal slope bounds and one bounded fitted point control the
whole affine test, including its constant coefficient. -/
theorem horizontal_test_coeffL1_bound (L x : Fin 4 → ℝ) {K a q : ℝ}
    (hK : 1 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1)
    (ht : x 0 ∈ Icc (0 : ℝ) 1) (hx : ∀ j, |x j| ≤ K)
    (hfit : |eval x (X 3 - affineBase L)| ≤ K * a)
    (hvertical : |L 3| ≤ K * (1 + a / q ^ 2))
    (hrow : |L 1 - x 1 * L 3| + |L 2 + x 0 * L 3| ≤ K * (1 + a / q)) :
    coeffL1 (X 3 - affineBase L) ≤ 40 * K ^ 3 * (q⁻¹) ^ 2 := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  let J : ℝ := (q⁻¹) ^ 2
  let A : ℝ := 4 * K ^ 2 * J
  have hJ0 : 0 ≤ J := sq_nonneg _
  have hJ1 : 1 ≤ J := one_le_pow₀ ((one_le_inv₀ hq).mpr hq1)
  have haJ : a / q ^ 2 ≤ J := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact (mul_le_mul_of_nonneg_right ha1 hJ0).trans_eq (one_mul _)
  obtain ⟨hL1, hL2, hL3⟩ :=
    Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.horizontal_affine_coeff_bounds
      L hK ha hq hq1 (hx 1) ht hvertical hrow
  have hcommon : 2 * K ^ 2 * (1 + a / q ^ 2) ≤ A := by
    calc
      _ ≤ 2 * K ^ 2 * (2 * J) :=
        mul_le_mul_of_nonneg_left (by linarith only [haJ, hJ1]) (by positivity)
      _ = _ := by dsimp only [A]; ring
  have h1 : |L 1| ≤ A := hL1.trans hcommon
  have h2 : |L 2| ≤ A := hL2.trans hcommon
  have h3 : |L 3| ≤ A := hL3.trans hcommon
  have ht1 : |x 0| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hprod1 : |L 1 * x 0| ≤ A := by
    rw [abs_mul]
    exact (mul_le_mul h1 ht1 (abs_nonneg _) (by dsimp only [A]; positivity)).trans_eq (mul_one _)
  have hprod2 : |L 2 * x 1| ≤ A * K := by
    rw [abs_mul]
    exact mul_le_mul h2 (hx 1) (abs_nonneg _) (by dsimp only [A]; positivity)
  have hprod3 : |L 3 * x 2| ≤ A * K := by
    rw [abs_mul]
    exact mul_le_mul h3 (hx 2) (abs_nonneg _) (by dsimp only [A]; positivity)
  let Z : ℝ := L 0 + L 1 * x 0 + L 2 * x 1 + L 3 * x 2
  have hfit' : |x 3 - Z| ≤ K := by
    have hh : |x 3 - Z| ≤ K * a := by
      simpa only [Z, affineBase, eval_sub, eval_add, eval_C, eval_mul, eval_X] using hfit
    exact hh.trans ((mul_le_mul_of_nonneg_left ha1 hK0).trans_eq (mul_one _))
  have h0 : |L 0| ≤ 2 * K + A + 2 * K * A := by
    have htri : |x 3 - (x 3 - Z) - L 1 * x 0 - L 2 * x 1 - L 3 * x 2| ≤
        |x 3| + |x 3 - Z| + |L 1 * x 0| + |L 2 * x 1| + |L 3 * x 2| := by
      have h1 := abs_sub (x 3) (x 3 - Z)
      have h2 := abs_sub (x 3 - (x 3 - Z)) (L 1 * x 0)
      have h3 := abs_sub (x 3 - (x 3 - Z) - L 1 * x 0) (L 2 * x 1)
      have h4 := abs_sub (x 3 - (x 3 - Z) - L 1 * x 0 - L 2 * x 1) (L 3 * x 2)
      linarith
    have heq : x 3 - (x 3 - Z) - L 1 * x 0 - L 2 * x 1 - L 3 * x 2 = L 0 := by
      dsimp only [Z]
      ring
    rw [heq] at htri
    linarith only [htri, hx 3, hfit', hprod1, hprod2, hprod3]
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hKK3 : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ 3 by norm_num)
  have hK23 : K ^ 2 ≤ K ^ 3 := pow_le_pow_right₀ hK (by norm_num)
  have h1C : 1 ≤ K ^ 3 * J := one_le_mul_of_one_le_of_one_le hK3 hJ1
  have hKC : K ≤ K ^ 3 * J :=
    hKK3.trans (le_mul_of_one_le_right (by positivity) hJ1)
  have h2C : K ^ 2 * J ≤ K ^ 3 * J := mul_le_mul_of_nonneg_right hK23 hJ0
  calc
    coeffL1 (X 3 - affineBase L) ≤ 1 + (|L 0| + |L 1| + |L 2| + |L 3|) := by
      exact (coeffL1_sub_le _ _).trans (by
        rw [coeffL1_X]
        exact add_le_add le_rfl (coeffL1_affineBase L))
    _ ≤ 1 + 2 * K + 4 * A + 2 * K * A := by linarith only [h0, h1, h2, h3]
    _ = 1 + 2 * K + 16 * (K ^ 2 * J) + 8 * (K ^ 3 * J) := by dsimp only [A]; ring
    _ ≤ 27 * (K ^ 3 * J) := by linarith only [h1C, hKC, h2C]
    _ ≤ _ := by dsimp only [J]; nlinarith only [mul_nonneg (pow_nonneg hK0 3) hJ0]

/-- At every fixed positive depth range, the tests of a horizontal model
have a uniform fixed-power coefficient bound. -/
theorem eventually_horizontal_test_coeffL1_power {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (hbasic : D.Basic) (hatlas : D.Atlas)
    {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ D.U → ∀ i : Fin (D.n k s),
      coeffL1 (D.F k s i) ≤ D.N k ^ (2 * D.U + 11) := by
  filter_upwards [hatlas R hR, p.subpower.2 1 (by norm_num)] with k hk hKN
  rw [Real.rpow_one] at hKN
  intro s hs hsU i
  have hN : 0 < D.N k := by linarith [p.scale k]
  have hN1 : 1 ≤ D.N k := by linarith [p.scale k]
  have hK : 1 ≤ D.K k := p.subpower.1 k
  have hK0 : 0 < D.K k := by linarith
  have hs0 : 0 ≤ s := (inv_pos.mpr (by linarith : 0 < R)).le.trans hs
  obtain ⟨hTlo, hTup, hmeas, hdisj, hlabels, hcover, hjoint⟩ := hk s hs hsU
  obtain ⟨hνlo, hνup, hμlo, hc, hdegree, hrows, hfit, hder, hhor⟩ := hlabels i
  obtain ⟨hP, hcontact, hcenter, L, hF, hv, hslopes⟩ := hhor rfl
  let q : ℝ := (2 : ℝ) ^ (-(D.T k s : ℤ))
  let a : ℝ := D.N k ^ (-s)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp only [q]
    rw [zpow_neg, zpow_natCast]
    exact (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have ha : 0 ≤ a := Real.rpow_nonneg hN.le _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hνpos : 0 < D.ν k (D.A k s i) := by
    apply lt_of_lt_of_le _ hνlo
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hμpos : 0 < D.μ k (D.B k s i ×ˢ Data.I (D.T k s) (D.j k s i)) := by
    apply lt_of_lt_of_le _ hμlo
    have hcpos : 0 < ENNReal.ofReal (q / D.K k) := ENNReal.ofReal_pos.mpr (div_pos hq hK0)
    exact bot_lt_iff_ne_bot.mpr (mul_ne_zero hcpos.ne' hνpos.ne')
  obtain ⟨z, hz, hbase, hnative⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    hμpos.ne' (ae_restrict_of_ae
      ((basic_base_bound D p.subpower.1 hbasic k).and (basic_native_value_bounds D hbasic k)))
  have ht : z.2 ∈ Icc (0 : ℝ) 1 :=
    Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit (D.T k s) (D.j k s i) hz.2
  have hx : ∀ j, |D.x k z.1 z.2 j| ≤ D.K k := by
    intro j
    fin_cases j
    · exact hbase 0
    · exact hbase 1
    · exact hbase 2
    · change |D.x k z.1 z.2 (3 : Fin 4)| ≤ D.K k
      simpa only [hP, eval_X] using hnative.1
  have hb := horizontal_test_coeffL1_bound L (D.x k z.1 z.2) hK ha ha1 hq hq1
    (by simpa only [Data.x, Matrix.cons_val_zero] using ht) hx
    (by simpa only [hF, affineBase] using (hfit z.1 hz.1 z.2 hz.2).1)
    hv (hslopes z.1 hz.1 z.2 hz.2)
  rw [hF] at ⊢
  change coeffL1 (X 3 - affineBase L) ≤ _
  have hqinv : q⁻¹ ≤ D.N k ^ (D.U + 1) := by
    have hκs : D.κ * s ≤ D.U := by
      calc
        D.κ * s ≤ 1 * s := mul_le_mul_of_nonneg_right p.rate_le_one hs0
        _ = s := one_mul _
        _ ≤ D.U := hsU
    calc
      q⁻¹ = (2 : ℝ) ^ D.T k s := by simp [q, zpow_neg, zpow_natCast]
      _ ≤ D.K k * D.N k ^ (D.κ * s) := hTup
      _ ≤ D.N k * D.N k ^ D.U :=
        mul_le_mul hKN (Real.rpow_le_rpow_of_exponent_le hN1 hκs)
          (Real.rpow_nonneg hN.le _) hN.le
      _ = _ := by rw [Real.rpow_add hN, Real.rpow_one]; ring
  have hq2 : (q⁻¹) ^ 2 ≤ D.N k ^ (2 * D.U + 2) := by
    calc
      _ ≤ (D.N k ^ (D.U + 1)) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hqinv 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; ring
  have h40 : (40 : ℝ) ≤ D.N k ^ (6 : ℕ) := by
    exact (by norm_num : (40 : ℝ) ≤ 2 ^ (6 : ℕ)).trans (pow_le_pow_left₀ (by norm_num) (p.scale k) 6)
  calc
    _ ≤ 40 * D.K k ^ 3 * (q⁻¹) ^ 2 := hb
    _ ≤ 40 * D.N k ^ (3 : ℕ) * D.N k ^ (2 * D.U + 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK0.le hKN 3) (by norm_num))
        hq2 (by positivity) (by positivity)
    _ ≤ D.N k ^ (6 : ℕ) * D.N k ^ (3 : ℕ) * D.N k ^ (2 * D.U + 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h40 (by positivity)) (by positivity)
    _ = D.N k ^ (2 * D.U + 11) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hN, ← Real.rpow_add hN]
      congr 1
      ring

/-- The exact coefficient budget in the horizontal candidate principle is
also bounded by a fixed power on every positive depth range. -/
theorem eventually_horizontal_coefficient_budget {α : Type} [MeasurableSpace α]
    (D : Data α) (p : Parameters D) (hbasic : D.Basic) (hatlas : D.Atlas)
    {R : ℝ} (hR : 1 < R) :
    ∀ᶠ k in atTop, ∀ s : ℝ, R⁻¹ ≤ s → s ≤ D.U → ∀ i : Fin (D.n k s),
      (1 + ∑ e ∈ (D.F k s i).support, |(D.F k s i).coeff e|) +
        ∑ e ∈ (X 3 : MvPolynomial (Fin 4) ℝ).support,
          |(X 3 : MvPolynomial (Fin 4) ℝ).coeff e| ≤ D.N k ^ (2 * D.U + 13) := by
  filter_upwards [eventually_horizontal_test_coeffL1_power D p hbasic hatlas hR] with k hk
  intro s hs hsU i
  have hN : 0 < D.N k := by linarith [p.scale k]
  have hN1 : 1 ≤ D.N k := by linarith [p.scale k]
  have hpow : 1 ≤ D.N k ^ (2 * D.U + 11) :=
    Real.one_le_rpow hN1 (by linarith [p.depth_pos])
  have h3 : (3 : ℝ) ≤ D.N k ^ (2 : ℕ) := by nlinarith [p.scale k]
  change 1 + coeffL1 (D.F k s i) + coeffL1 (X (3 : Fin 4)) ≤ _
  rw [coeffL1_X]
  calc
    _ ≤ 3 * D.N k ^ (2 * D.U + 11) := by linarith only [hk s hs hsU i, hpow]
    _ ≤ D.N k ^ (2 : ℕ) * D.N k ^ (2 * D.U + 11) :=
      mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hN.le _)
    _ = D.N k ^ (2 * D.U + 13) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN]
      congr 1
      ring

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Shifted
