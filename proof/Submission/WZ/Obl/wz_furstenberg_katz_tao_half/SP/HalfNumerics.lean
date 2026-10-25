-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.HalfNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.HalfEndgameCore
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PowerBudget

/-!
# Closed forms of the quantities of `half_endgame_core` for `K = r ^ (-κ)`, `c = r ^ κ`
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

section ClosedForms

variable {u κ : ℝ} (hu : 0 < u)
include hu

theorem cf_csq : (u ^ κ) ^ 2 = u ^ (2 * κ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 1
  push_cast
  ring

theorem cf_delta : 16384 * u / (u ^ κ) ^ 2 = 16384 * u ^ (1 - 2 * κ) := by
  rw [cf_csq hu, mul_div_assoc, Real.rpow_sub hu, Real.rpow_one]

theorem cf_ratio : 6600 * (16384 * u / (u ^ κ) ^ 2) / ((u ^ κ) ^ 2 * u) =
    6600 * 16384 * u ^ (-(4 * κ)) := by
  rw [cf_delta hu, cf_csq hu]
  have e : u ^ (-(4 * κ)) = u ^ (1 - 2 * κ) / (u ^ (2 * κ) * u) := by
    rw [← Real.rpow_add_one hu.ne', ← Real.rpow_sub hu]
    congr 1
    ring
  rw [e]
  ring

theorem cf_M : 225 * (6600 * (16384 * u / (u ^ κ) ^ 2) / ((u ^ κ) ^ 2 * u)) ^ 2 =
    225 * (6600 * 16384) ^ 2 * u ^ (-(8 * κ)) := by
  rw [cf_ratio hu, mul_pow, ← Real.rpow_natCast (u ^ (-(4 * κ))), ← Real.rpow_mul hu.le]
  push_cast
  ring_nf

theorem cf_sqrt_div : (2 / u) ^ (1 / 2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) * u ^ (-(1 / 2 : ℝ)) := by
  rw [Real.div_rpow (by norm_num) hu.le, Real.rpow_neg hu.le, div_eq_mul_inv]

theorem cf_Kb : u ^ (-κ) * (2 / u) ^ (1 / 2 : ℝ) =
    (2 : ℝ) ^ (1 / 2 : ℝ) * u ^ (-κ - 1 / 2) := by
  rw [cf_sqrt_div hu]
  have e : u ^ (-κ - 1 / 2) = u ^ (-κ) * u ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hu]
    congr 1
  rw [e]
  ring

theorem cf_Lg : (u ^ (-κ) * u ^ (-κ) * u * (225 * (6600 * 16384) ^ 2 * u ^ (-(8 * κ))))⁻¹ =
    u ^ (10 * κ - 1) / (225 * (6600 * 16384) ^ 2) := by
  have e : u ^ (-κ) * u ^ (-κ) * u * u ^ (-(8 * κ)) = u ^ (1 - 10 * κ) := by
    rw [← Real.rpow_add hu, ← Real.rpow_add_one hu.ne', ← Real.rpow_add hu]
    congr 1
    ring
  have e2 : u ^ (10 * κ - 1) = (u ^ (1 - 10 * κ))⁻¹ := by
    rw [← Real.rpow_neg hu.le]
    congr 1
    ring
  rw [e2]
  have e3 : u ^ (-κ) * u ^ (-κ) * u * (225 * (6600 * 16384) ^ 2 * u ^ (-(8 * κ))) =
      225 * (6600 * 16384) ^ 2 * (u ^ (-κ) * u ^ (-κ) * u * u ^ (-(8 * κ))) := by ring
  rw [e3, e, mul_inv, div_eq_mul_inv, mul_comm]

theorem cf_La : u ^ (10 * κ - 1) / (225 * (6600 * 16384) ^ 2) /
    ((2 : ℝ) ^ (1 / 2 : ℝ) * u ^ (-κ - 1 / 2)) =
      u ^ (11 * κ - 1 / 2) / (225 * (6600 * 16384) ^ 2 * (2 : ℝ) ^ (1 / 2 : ℝ)) := by
  have e : u ^ (11 * κ - 1 / 2) = u ^ (10 * κ - 1) / u ^ (-κ - 1 / 2) := by
    rw [← Real.rpow_sub hu]
    congr 1
    ring
  rw [e]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hp : 0 < u ^ (-κ - 1 / 2) := Real.rpow_pos_of_pos hu _
  field_simp

theorem cf_sq4 : (4 / (u ^ κ / 64 * u)) ^ (1 / 2 : ℝ) = 16 * u ^ (-(κ + 1) / 2) := by
  have e : 4 / (u ^ κ / 64 * u) = 256 * u ^ (-(κ + 1)) := by
    rw [Real.rpow_neg hu.le, Real.rpow_add_one hu.ne']
    field_simp
    ring
  rw [e, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le]
  have h256 : (256 : ℝ) ^ (1 / 2 : ℝ) = 16 := by
    rw [show (256 : ℝ) = 16 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h256]
  congr 2
  ring

theorem cf_CA : 2 * u ^ (-κ) * (4 / (u ^ κ / 64 * u)) ^ (1 / 2 : ℝ) /
    (u ^ (11 * κ - 1 / 2) / (225 * (6600 * 16384) ^ 2 * (2 : ℝ) ^ (1 / 2 : ℝ))) =
      32 * (225 * (6600 * 16384) ^ 2 * (2 : ℝ) ^ (1 / 2 : ℝ)) * u ^ (-(25 / 2 * κ)) := by
  rw [cf_sq4 hu]
  have e : u ^ (-(25 / 2 * κ)) = u ^ (-κ) * u ^ (-(κ + 1) / 2) / u ^ (11 * κ - 1 / 2) := by
    rw [← Real.rpow_add hu, ← Real.rpow_sub hu]
    congr 1
    ring
  rw [e]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hp : 0 < u ^ (11 * κ - 1 / 2) := Real.rpow_pos_of_pos hu _
  field_simp
  ring

theorem cf_delta_rpow (a : ℝ) : (16384 * u ^ (1 - 2 * κ)) ^ a = 16384 ^ a * u ^ ((1 - 2 * κ) * a) := by
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hu.le _), ← Real.rpow_mul hu.le]

end ClosedForms

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
