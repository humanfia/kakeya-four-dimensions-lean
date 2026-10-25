import Mathlib

namespace Submission.Obl.k4_pair_anchor_jet_bins

open Filter

/-- A fixed gap between exponents absorbs an arbitrary fixed multiplier. -/
theorem eventually_mul_power_le (C : ℝ) {p q : ℝ} (hpq : p < q) :
    ∀ᶠ A : ℝ in atTop, C * A ^ p ≤ A ^ q := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hpq)).eventually_ge_atTop C
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with A hCA hA
  calc
    C * A ^ p ≤ A ^ (q - p) * A ^ p :=
      mul_le_mul_of_nonneg_right hCA (Real.rpow_nonneg hA.le _)
    _ = A ^ q := by rw [← Real.rpow_add hA]; congr 1; ring

/-- The source-to-anchor and anchor-to-source losses are powers of the same base. -/
theorem power_mul_scale {A : ℝ} (hA : 0 < A) (k C V δ : ℝ) :
    (A ^ k) ^ C * (δ * A ^ V) = δ * A ^ (k * C + V) := by
  rw [← Real.rpow_mul hA.le]
  calc
    A ^ (k * C) * (δ * A ^ V) = δ * (A ^ (k * C) * A ^ V) := by ring
    _ = δ * A ^ (k * C + V) := by rw [← Real.rpow_add hA]

/-- Bound the expression supplied by the reverse continuation comparison. -/
theorem return_expression_bound {A δ k C₁ C₂ V C c : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hc0 : 0 ≤ c) (hc : c ≤ δ⁻¹)
    (hE : 2 ≤ k * C₁ + V)
    (habsorb : 2 * A ^ (k * C₂ + 2 * (k * C₁ + V)) ≤ A ^ C) :
    (A ^ k) ^ C₂ * (((A ^ k) ^ C₁ * (δ * A ^ V)) *
      (A ^ (2 : ℕ) + c / 2 * ((A ^ k) ^ C₁ * (δ * A ^ V)))) ≤ δ * A ^ C := by
  have hA0 : 0 < A := by linarith
  rw [power_mul_scale hA0]
  have hsmall : c / 2 * (δ * A ^ (k * C₁ + V)) ≤ A ^ (k * C₁ + V) := by
    calc
      _ ≤ δ⁻¹ * (δ * A ^ (k * C₁ + V)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith [inv_pos.mpr hδ]
      _ = _ := by field_simp
  have h2 : A ^ (2 : ℕ) ≤ A ^ (k * C₁ + V) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hA hE
  calc
    _ ≤ (A ^ k) ^ C₂ * ((δ * A ^ (k * C₁ + V)) * (2 * A ^ (k * C₁ + V))) := by
      gcongr
      linarith
    _ = δ * (2 * A ^ (k * C₂ + 2 * (k * C₁ + V))) := by
      rw [← Real.rpow_mul hA0.le]
      calc
        _ = δ * (2 * ((A ^ (k * C₂) * A ^ (k * C₁ + V)) * A ^ (k * C₁ + V))) := by ring
        _ = _ := by rw [← Real.rpow_add hA0, ← Real.rpow_add hA0]; congr 3; ring
    _ ≤ δ * A ^ C := mul_le_mul_of_nonneg_left habsorb hδ.le

/-- The quadratic hidden-variable perturbation preserves a polynomial loss. -/
theorem transfer_expression_bound {A C K : ℝ} (hA : 1 ≤ A) (hC : 2 ≤ C)
    (habsorb : 6 * A ^ (C + 1) ≤ A ^ K) :
    A ^ C + A * (A ^ (2 : ℕ) + 2 * A ^ C + 1 + A) ≤ A ^ K ∧
      A ^ (2 : ℕ) + 2 * A ^ C + 1 + A ≤ A ^ K := by
  have hA0 : 0 < A := by linarith
  have h2 : A ^ (2 : ℕ) ≤ A ^ C := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hA hC
  have h1 : 1 ≤ A ^ C := Real.one_le_rpow hA (by linarith)
  have hlin : A ≤ A ^ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA (show (1 : ℝ) ≤ C by linarith)
  have hsum : A ^ (2 : ℕ) + 2 * A ^ C + 1 + A ≤ 5 * A ^ C := by linarith
  have hpow : A ^ (C + 1) = A * A ^ C := by rw [Real.rpow_add hA0, Real.rpow_one]; ring
  constructor
  · calc
      _ ≤ A ^ C + A * (5 * A ^ C) := by gcongr
      _ ≤ 6 * A ^ (C + 1) := by rw [hpow]; nlinarith [Real.rpow_nonneg hA0.le C]
      _ ≤ A ^ K := habsorb
  · calc
      _ ≤ 5 * A ^ C := hsum
      _ ≤ 6 * A ^ (C + 1) := by rw [hpow]; nlinarith [Real.rpow_nonneg hA0.le C]
      _ ≤ A ^ K := habsorb

/-- A slightly shorter power interval fits the continuation ball and the local trajectory fit. -/
theorem eventually_short_radius {k : ℝ} (hk : 1 ≤ k) :
    ∀ᶠ A : ℝ in atTop,
      A ^ (-(k + 2)) ≤ (8 * A ^ k)⁻¹ ∧ A ^ (-(k + 2)) ≤ A⁻¹ / 100 := by
  filter_upwards [eventually_mul_power_le 8 (p := -(k + 2)) (q := -k) (by linarith),
    eventually_mul_power_le 100 (p := -(k + 2)) (q := -1) (by linarith),
    eventually_gt_atTop (0 : ℝ)] with A h8 h100 hA
  rw [Real.rpow_neg hA.le (1 : ℝ), Real.rpow_one] at h100
  constructor
  · rw [Real.rpow_neg hA.le k] at h8
    rw [mul_inv]
    nlinarith
  · linarith

end Submission.Obl.k4_pair_anchor_jet_bins
