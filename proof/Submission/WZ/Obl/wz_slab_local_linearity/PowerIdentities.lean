-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.PowerIdentities.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_slab_local_linearity

lemma rpow_nat_power {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ) (n : ℕ) :
    (ρ ^ a) ^ n = ρ ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]

lemma cell_denominator_power {ρ : ℝ} (hρ : 0 < ρ) (σ η : ℝ) :
    (ρ ^ (-(1 - σ) / 2 - η)) ^ 4 / ((Real.sqrt ρ) ^ 5 * (ρ ^ η) ^ 2) =
      ρ ^ (-(9 : ℝ) / 2 + 2 * σ - 6 * η) := by
  rw [Real.sqrt_eq_rpow, rpow_nat_power hρ, rpow_nat_power hρ, rpow_nat_power hρ,
    ← Real.rpow_add hρ, ← Real.rpow_sub hρ]
  congr 1
  norm_num
  ring

lemma cell_rich_power {ρ : ℝ} (hρ : 0 < ρ) (σ η : ℝ) :
    (ρ ^ (-(1 - σ) / 2 - η)) ^ 2 / (Real.sqrt ρ * ρ ^ η) =
      ρ ^ (-(3 : ℝ) / 2 + σ - 3 * η) := by
  rw [Real.sqrt_eq_rpow, rpow_nat_power hρ, ← Real.rpow_add hρ, ← Real.rpow_sub hρ]
  congr 1
  norm_num
  ring

lemma cell_fourth_power {ρ : ℝ} (hρ : 0 < ρ) (σ η : ℝ) :
    (ρ ^ (-2 + σ / 2 + η) * Real.sqrt ρ / 4) ^ 4 =
      ρ ^ (-6 + 2 * σ + 4 * η) / 256 := by
  rw [div_pow, mul_pow, Real.sqrt_eq_rpow, rpow_nat_power hρ, rpow_nat_power hρ,
    ← Real.rpow_add hρ]
  norm_num
  congr 1
  ring

lemma cell_multiplicity_power {ρ : ℝ} (hρ : 0 < ρ) (η : ℝ) :
    (100 / ρ ^ η) ^ 3 = 1000000 * ρ ^ (-3 * η) := by
  rw [div_pow, rpow_nat_power hρ, div_eq_mul_inv, ← Real.rpow_neg hρ.le]
  norm_num
  congr 1
  congr 1
  ring

lemma cell_delta_power_upper {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    (Real.sqrt ρ / 1000) ^ (τ - 3) ≤ 1000000000 * ρ ^ (τ / 2 - 3 / 2) := by
  rw [Real.div_rpow (Real.sqrt_nonneg ρ) (by norm_num), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hρ.le]
  have he : (1 / 2 : ℝ) * (τ - 3) = τ / 2 - 3 / 2 := by ring
  rw [he, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1000)]
  have hc : (1000 : ℝ) ^ (-(τ - 3)) ≤ 1000000000 := by
    calc (1000 : ℝ) ^ (-(τ - 3)) ≤ (1000 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1000000000 := by norm_num
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hρ.le _)

lemma sqrt_div_self_rpow {ρ : ℝ} (hρ : 0 < ρ) :
    Real.sqrt ρ / ρ = ρ ^ (-(1 : ℝ) / 2) := by
  calc Real.sqrt ρ / ρ = ρ ^ ((1 : ℝ) / 2) / ρ ^ (1 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_one]
    _ = ρ ^ ((1 : ℝ) / 2 - 1) := (Real.rpow_sub hρ _ _).symm
    _ = ρ ^ (-(1 : ℝ) / 2) := by norm_num

lemma global_cover_power_bound {ρ σ η : ℝ} (hρ : 0 < ρ) (hσ : 0 ≤ σ) :
    ρ ^ (-η) * (4 * Real.sqrt ρ / ρ) ^ (1 - σ) ≤
      4 * ρ ^ (-(1 - σ) / 2 - η) := by
  have he : 4 * Real.sqrt ρ / ρ = 4 * ρ ^ (-(1 : ℝ) / 2) := by
    rw [mul_div_assoc, sqrt_div_self_rpow hρ]
  rw [he, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
  have hp : (4 : ℝ) ^ (1 - σ) ≤ 4 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by linarith)
  calc ρ ^ (-η) * ((4 : ℝ) ^ (1 - σ) * ρ ^ (-(1 : ℝ) / 2 * (1 - σ)))
      = (4 : ℝ) ^ (1 - σ) * ρ ^ (-(1 - σ) / 2 - η) := by
        rw [mul_left_comm, ← Real.rpow_add hρ]
        congr 2
        ring
    _ ≤ 4 * ρ ^ (-(1 - σ) / 2 - η) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hρ.le _)

lemma local_cover_power_eq {ρ : ℝ} (hρ : 0 < ρ) (σ η : ℝ) :
    ρ ^ ((1 + σ) / 2 - η) / ρ = ρ ^ (-(1 - σ) / 2 - η) := by
  rw [← Real.rpow_sub_one hρ.ne']
  congr 1
  ring

end WangZahlLot.Obl.wz_slab_local_linearity
