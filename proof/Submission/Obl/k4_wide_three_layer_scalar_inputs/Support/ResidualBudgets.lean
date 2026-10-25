import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics
import Submission.Obl.k4_scalar_grid_cartesian_field.HeavyCells

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open Filter
open scoped ENNReal

/-- Multiplying the residual table by the squared base mesh cancels its base-grid
cardinality. Only the original geometric slack and residual palette count remain. -/
theorem residual_table_normalized_bound {I : Type} (Fs : Finset I)
    {N m Kz B d v : ℝ} (hN : 1 ≤ N) (hm : 0 ≤ m) (hKz : 1 ≤ Kz) (hB : 0 ≤ B)
    (hcard : (Fs.card : ℝ) ≤ (N ^ m + 2) * (2 * Kz * N ^ m + 2) * (B * N ^ (d * v) * 7)) :
    (Fs.card : ℝ) * (N ^ (-m)) ^ 2 ≤ 84 * Kz * B * N ^ (d * v) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hmone : 1 ≤ N ^ m := Real.one_le_rpow hN hm
  have hKz₀ : 0 ≤ Kz := zero_le_one.trans hKz
  have hgrid : (N ^ m + 2) * (2 * Kz * N ^ m + 2) ≤ 12 * Kz * (N ^ m) ^ 2 := by
    calc
      _ ≤ (3 * N ^ m) * (4 * Kz * N ^ m) := by
        apply mul_le_mul
        · linarith
        · nlinarith [mul_le_mul_of_nonneg_right hKz (Real.rpow_nonneg hN₀.le m)]
        · positivity
        · positivity
      _ = _ := by ring
  have hcancel : (N ^ m) ^ 2 * (N ^ (-m)) ^ 2 = 1 := by
    rw [← mul_pow, ← Real.rpow_add hN₀, add_neg_cancel, Real.rpow_zero, one_pow]
  calc
    _ ≤ ((N ^ m + 2) * (2 * Kz * N ^ m + 2) * (B * N ^ (d * v) * 7)) *
        (N ^ (-m)) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ ≤ (12 * Kz * (N ^ m) ^ 2 * (B * N ^ (d * v) * 7)) * (N ^ (-m)) ^ 2 := by
      gcongr
    _ = (84 * Kz * B * N ^ (d * v)) * ((N ^ m) ^ 2 * (N ^ (-m)) ^ 2) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- An inverse power cutoff pays the residual pruning while leaving a power floor
on the same original block reference. -/
theorem residual_pruning_mass_floor {N η : ℝ} (hN : 0 < N) (hlarge : 54 ≤ N ^ η)
    {W total kept : ℝ≥0∞} (hW : W ≠ ⊤)
    (hfloor : ENNReal.ofReal (N ^ (-η)) * W ≤ total)
    (hloss : total ≤ kept + ENNReal.ofReal (N ^ (-2 * η)) * ((27 : ℝ≥0∞) * W)) :
    ENNReal.ofReal (N ^ (-2 * η)) * W ≤ kept := by
  have hpow : N ^ η * N ^ (-2 * η) = N ^ (-η) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have h54 : 54 * N ^ (-2 * η) ≤ N ^ (-η) := by
    have hh := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hN.le (-2 * η))
    simpa only [hpow] using hh
  have hp : 0 ≤ N ^ (-2 * η) := Real.rpow_nonneg hN.le _
  have ha : 0 ≤ N ^ (-η) / 2 := by positivity
  have hcost : 27 * N ^ (-2 * η) ≤ N ^ (-η) / 2 := by linarith
  have hsmall : N ^ (-2 * η) ≤ N ^ (-η) / 2 := by linarith
  let a := ENNReal.ofReal (N ^ (-η) / 2) * W
  have hdouble : a + a ≤ total := by
    have heq : a + a = ENNReal.ofReal (N ^ (-η)) * W := by
      dsimp only [a]
      rw [← add_mul, ← ENNReal.ofReal_add ha ha]
      congr 2
      ring
    exact heq.le.trans hfloor
  have hcost' : ENNReal.ofReal (N ^ (-2 * η)) * ((27 : ℝ≥0∞) * W) ≤ a := by
    have hh := mul_le_mul' (ENNReal.ofReal_le_ofReal hcost) (le_refl W)
    convert hh using 1 <;> simp only [ENNReal.ofReal_mul (by norm_num : 0 ≤ (27 : ℝ)),
      ENNReal.ofReal_ofNat] <;> ring
  have hkeep := Submission.Obl.k4_scalar_grid_cartesian_field.pruning_mass_floor
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW) hdouble hloss hcost'
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hsmall) le_rfl).trans hkeep

/-- Subpower geometric, chart and coefficient costs and the original inverse-power
cutoff fit the final frozen support budget at every requested positive loss. -/
theorem eventually_residual_table_budget {η θ : ℝ} (hη : 0 ≤ η) (hmargin : 8 * η < θ) :
    ∀ᶠ N : ℝ in atTop, ∀ K Kz H M₀ m d v : ℝ,
      1 ≤ K → K ≤ N ^ η → 1 ≤ Kz → Kz ≤ N ^ η →
      0 ≤ H → H ≤ N ^ η → 0 ≤ M₀ → M₀ ≤ N ^ η → 0 ≤ m →
      ∀ {I : Type} (Fs : Finset I),
      (Fs.card : ℝ) ≤ (N ^ m + 2) * (2 * Kz * N ^ m + 2) *
        ((ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * η))).toReal *
          M₀ * H ^ 3 * N ^ (d * v) * 7) →
      (Fs.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ θ * (N ^ (-v)) ^ (-d) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 84 hmargin]
    with N hN hbudget
  intro K Kz H M₀ m d v hK hKN hKz hKzN hH hHN hM₀ hM₀N hm I Fs hcard
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hK₀ : 0 ≤ K := zero_le_one.trans hK
  have hratio : (ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * η))).toReal ≤ N ^ (3 * η) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hK₀,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hN₀.le _), div_eq_mul_inv,
      ← Real.rpow_neg hN₀.le, neg_mul, neg_neg]
    calc
      _ ≤ N ^ η * N ^ (2 * η) := by gcongr
      _ = _ := by rw [← Real.rpow_add hN₀]; congr 1; ring
  have hnormalized := residual_table_normalized_bound Fs hN hm hKz
    (show 0 ≤ (ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * η))).toReal * M₀ * H ^ 3 by positivity)
    hcard
  have hpower : N ^ η * N ^ (3 * η) * N ^ η * (N ^ η) ^ 3 = N ^ (8 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN₀.le,
      ← Real.rpow_add hN₀, ← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
    congr 1
    ring
  have hlast : N ^ (d * v) = (N ^ (-v)) ^ (-d) := by
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  calc
    _ ≤ 84 * Kz * ((ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * η))).toReal * M₀ * H ^ 3) *
        N ^ (d * v) := hnormalized
    _ ≤ 84 * N ^ η * (N ^ (3 * η) * N ^ η * (N ^ η) ^ 3) * N ^ (d * v) := by gcongr
    _ = (84 * (N ^ η * N ^ (3 * η) * N ^ η * (N ^ η) ^ 3)) * N ^ (d * v) := by ring
    _ = (84 * N ^ (8 * η)) * N ^ (d * v) := by rw [hpower]
    _ ≤ N ^ θ * N ^ (d * v) := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hN₀.le _)
    _ = _ := by rw [hlast]

/-- The literal counting cost in `extractionAt_of_corrected_fit` is absorbed by
independent subpower bounds for the native and corrected-fit constants. -/
theorem eventually_residual_extraction_count {κ ξ η θ : ℝ}
    (hmargin : 3 * κ + 3 * ξ + 2 * η < θ) :
    ∀ᶠ N : ℝ in atTop, ∀ K H : ℝ, 0 ≤ K → 0 ≤ H → K ≤ N ^ κ → H ≤ N ^ ξ →
      84 * K * ((ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * η))).toReal *
        (48 * K) * H ^ 3) ≤ N ^ θ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      4032 hmargin] with N hN hbudget
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  intro K H hK hH hKN hHN
  have hratio : (ENNReal.ofReal K / ENNReal.ofReal (N ^ (-2 * η))).toReal = K * N ^ (2 * η) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hK,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hN₀.le _), div_eq_mul_inv, ← Real.rpow_neg hN₀.le]
    congr 2
    ring
  have hpower : (N ^ κ) ^ 3 * (N ^ ξ) ^ 3 * N ^ (2 * η) = N ^ (3 * κ + 3 * ξ + 2 * η) := by
    rw [← Real.rpow_natCast (N ^ κ) 3, ← Real.rpow_natCast (N ^ ξ) 3,
      ← Real.rpow_mul hN₀.le, ← Real.rpow_mul hN₀.le,
      ← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
    congr 1
    ring
  rw [hratio]
  calc
    _ = 4032 * (K ^ 3 * H ^ 3 * N ^ (2 * η)) := by ring
    _ ≤ 4032 * ((N ^ κ) ^ 3 * (N ^ ξ) ^ 3 * N ^ (2 * η)) := by gcongr
    _ = 4032 * N ^ (3 * κ + 3 * ξ + 2 * η) := by rw [hpower]
    _ ≤ _ := hbudget

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
