-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.ProductSumNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PowerBudget

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

theorem scaled_error_budget {δ η ξ : ℝ} (hδ : 0 < δ)
    (hbudget : (9 : ℝ) ^ ξ * δ ^ (ξ - η) ≤ 1) :
    δ ^ (-η) ≤ (9 * δ) ^ (-ξ) := by
  rw [Real.rpow_neg (by positivity : 0 ≤ 9 * δ), inv_eq_one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < 9 * δ) ξ)).mpr
  calc
    δ ^ (-η) * (9 * δ) ^ ξ = (9 : ℝ) ^ ξ * δ ^ (ξ - η) := by
      rw [Real.mul_rpow (by norm_num) hδ.le]
      calc δ ^ (-η) * (9 ^ ξ * δ ^ ξ) = 9 ^ ξ * (δ ^ (-η) * δ ^ ξ) := by ring
        _ = _ := by rw [← Real.rpow_add hδ]; congr 2; ring
    _ ≤ 1 := hbudget

theorem grid_power_lower {δ η σ C G : ℝ} (hδ : 0 < δ) (hG : 0 ≤ G)
    (hC : C ≤ δ ^ (-η)) (hcount : 1 ≤ G * C * δ ^ σ) :
    δ ^ (η - σ) ≤ G := by
  have hh : 1 ≤ G * δ ^ (σ - η) := by
    calc 1 ≤ G * C * δ ^ σ := hcount
      _ ≤ G * δ ^ (-η) * δ ^ σ := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hδ.le (η - σ))
  have hid : δ ^ (σ - η) * δ ^ (η - σ) = 1 := by rw [← Real.rpow_add hδ]; simp
  simpa only [one_mul, mul_assoc, hid, mul_one] using hm

theorem nine_scale_power_lower {δ σ g : ℝ} (hδ : 0 < δ) (hσ : σ ≤ 1) (hg1 : g ≤ 1)
    (hbudget : 81 * δ ^ (g / 2) ≤ 1) :
    δ ^ (-σ - g / 2) ≤ (9 * δ) ^ (-σ - g) := by
  have hnine : (1 / 81 : ℝ) ≤ 9 ^ (-σ - g) := by
    calc (1 / 81 : ℝ) = 9 ^ (-2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlow : 81 * δ ^ (-σ - g / 2) ≤ δ ^ (-σ - g) := by
    calc
      81 * δ ^ (-σ - g / 2) = (81 * δ ^ (g / 2)) * δ ^ (-σ - g) := by
        rw [mul_assoc, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ 1 * δ ^ (-σ - g) := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hδ.le _)
      _ = _ := one_mul _
  calc
    δ ^ (-σ - g / 2) ≤ (1 / 81) * δ ^ (-σ - g) := by linarith
    _ ≤ 9 ^ (-σ - g) * δ ^ (-σ - g) :=
      mul_le_mul_of_nonneg_right hnine (Real.rpow_nonneg hδ.le _)
    _ = _ := (Real.mul_rpow (by norm_num) hδ.le).symm

/-- A ninth-power Plunnecke bound transfers the long-expression gain to a
sum of two products, with fixed power reserves. -/
theorem ninth_power_growth {δ σ η g n G m : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hηg : η ≤ g / 100) (hg : 0 < g) (hm : 0 ≤ m) (hG : 0 ≤ G)
    (hn : δ ^ (-σ - g / 2) ≤ n) (hGlow : δ ^ (η - σ) ≤ G)
    (hP : n * G ^ 8 ≤ (6 * m) ^ 9)
    (hbudget : (6 : ℝ) ^ 9 * δ ^ (g / 4) ≤ 1) :
    δ ^ (-σ - g / 100) ≤ m := by
  let a := -9 * σ - g / 2 + 8 * η
  have htop : δ ^ a ≤ (6 * m) ^ 9 := by
    calc
      δ ^ a = δ ^ (-σ - g / 2) * (δ ^ (η - σ)) ^ 8 := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ]
        congr 1
        dsimp [a]
        norm_num
        ring
      _ ≤ n * G ^ 8 := mul_le_mul hn (by gcongr) (by positivity)
        (le_trans (Real.rpow_nonneg hδ.le _) hn)
      _ ≤ _ := hP
  have hp : δ ^ (41 * g / 100 - 8 * η) ≤ δ ^ (g / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hc : (6 : ℝ) ^ 9 * δ ^ (41 * g / 100 - 8 * η) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (by positivity)).trans hbudget
  have hlow : (6 : ℝ) ^ 9 * (δ ^ (-σ - g / 100)) ^ 9 ≤ δ ^ a := by
    calc
      (6 : ℝ) ^ 9 * (δ ^ (-σ - g / 100)) ^ 9 =
          ((6 : ℝ) ^ 9 * δ ^ (41 * g / 100 - 8 * η)) * δ ^ a := by
        rw [← Real.rpow_mul_natCast hδ.le, mul_assoc, ← Real.rpow_add hδ]
        congr 1
        dsimp [a]
        norm_num
        ring
      _ ≤ 1 * δ ^ a := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hδ.le a)
      _ = _ := one_mul _
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hδ.le _) hm (by decide : (9 : ℕ) ≠ 0)).mp
  have hh := hlow.trans htop
  rw [mul_pow] at hh
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 6 ^ 9)).mp hh

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
