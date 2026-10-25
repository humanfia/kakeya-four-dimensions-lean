-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.RingNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.PowerBudget

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

theorem ring_ratio_scale {δ κ : ℝ} (hδ : 0 < δ) :
    16 * δ / (δ ^ (100 * κ) * δ ^ (100 * κ)) = 16 * δ ^ (1 - 200 * κ) := by
  rw [← Real.rpow_add hδ, Real.rpow_sub hδ, Real.rpow_one]
  congr 2
  congr 1
  ring

/-- Parameter bounds for the truncated ratio family. -/
theorem ring_scale_budget {δ κ σ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 10000) (hσ : 1 / 2 ≤ σ)
    (hC : C ≤ δ ^ (-κ)) (hsmall : 128 * δ ^ κ ≤ 1) :
    δ ≤ δ ^ (100 * κ) ∧ δ ^ (100 * κ) ≤ 1 ∧
      C * (δ ^ (100 * κ)) ^ σ < 1 := by
  refine ⟨?_, Real.rpow_le_one hδ.le hδ1 (by positivity), ?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 100 * κ ≤ 1)
  · have hp : δ ^ (100 * κ * σ - κ) ≤ δ ^ κ :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    calc
      C * (δ ^ (100 * κ)) ^ σ ≤ δ ^ (-κ) * (δ ^ (100 * κ)) ^ σ :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = δ ^ (100 * κ * σ - κ) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ κ := hp
      _ < 1 := by have := Real.rpow_pos_of_pos hδ κ; nlinarith

/-- The escaping-ratio branch gives a strict exponent gain. -/
theorem ring_sparse_power_gain {δ κ σ C N : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hCb : C ≤ δ ^ (-κ)) (hN : 0 ≤ N) (hsmall : 128 * δ ^ κ ≤ 1)
    (hcount : 1 ≤ C ^ 3 * (128 * δ * δ ^ (100 * κ)) ^ σ * N) :
    δ ^ (-σ - 10 * κ) ≤ N := by
  let a := σ + 100 * κ * σ - 3 * κ
  have hC3 : C ^ 3 ≤ δ ^ (-3 * κ) := by
    calc C ^ 3 ≤ (δ ^ (-κ)) ^ 3 := by gcongr
      _ = δ ^ (-3 * κ) := by rw [← Real.rpow_mul_natCast hδ.le]; congr 1; norm_num; ring
  have h128 : (128 : ℝ) ^ σ ≤ 128 := by
    calc (128 : ℝ) ^ σ ≤ 128 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
      _ = _ := Real.rpow_one _
  have hcoeff : C ^ 3 * (128 * δ * δ ^ (100 * κ)) ^ σ ≤ 128 * δ ^ a := by
    calc
      C ^ 3 * (128 * δ * δ ^ (100 * κ)) ^ σ ≤
          δ ^ (-3 * κ) * (128 * δ * δ ^ (100 * κ)) ^ σ := by gcongr
      _ = (128 : ℝ) ^ σ * δ ^ a := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num) hδ.le, ← Real.rpow_mul hδ.le]
        calc
          δ ^ (-3 * κ) * (128 ^ σ * δ ^ σ * δ ^ (100 * κ * σ)) =
              128 ^ σ * ((δ ^ (-3 * κ) * δ ^ σ) * δ ^ (100 * κ * σ)) := by ring
          _ = _ := by rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 2; dsimp [a]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h128 (Real.rpow_nonneg hδ.le a)
  have hlow : (128 * δ ^ a) * δ ^ (-σ - 10 * κ) ≤ 1 := by
    calc
      (128 * δ ^ a) * δ ^ (-σ - 10 * κ) = 128 * δ ^ (100 * κ * σ - 13 * κ) := by
        rw [mul_assoc, ← Real.rpow_add hδ]; congr 1; dsimp [a]; ring
      _ ≤ 128 * δ ^ κ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)) (by norm_num)
      _ ≤ 1 := hsmall
  have hupper := hcount.trans (mul_le_mul_of_nonneg_right hcoeff hN)
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 128 * δ ^ a)).mp (hlow.trans hupper)

/-- The dense-ratio branch gives a strict exponent gain, uniformly in
`σ ≤ 1 - 10000κ`. -/
theorem ring_dense_power_gain {δ κ σ C N : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 10000) (hσmax : σ ≤ 1 - 10000 * κ)
    (hC : 0 ≤ C) (hCb : C ≤ δ ^ (-κ)) (hN : 0 ≤ N)
    (hsmall : 128 * δ ^ κ ≤ 1)
    (hcount : (16 * δ / (δ ^ (100 * κ) * δ ^ (100 * κ))) ^ (2500 * κ - 1) ≤
      (max (C * C) 40) ^ 2 * N) :
    δ ^ (-σ - 10 * κ) ≤ N := by
  let a := (1 - 200 * κ) * (2500 * κ - 1) + 4 * κ
  have hforty : 40 ≤ δ ^ (-2 * κ) := by
    have hp : δ ^ (2 * κ) ≤ δ ^ κ :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    rw [show (-2 : ℝ) * κ = -(2 * κ) by ring, Real.rpow_neg hδ.le, inv_eq_one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr
    have := Real.rpow_pos_of_pos hδ κ
    nlinarith
  have hCC : C * C ≤ δ ^ (-2 * κ) := by
    calc C * C ≤ δ ^ (-κ) * δ ^ (-κ) := mul_le_mul hCb hCb hC (by positivity)
      _ = _ := by rw [← Real.rpow_add hδ]; congr 1; ring
  have hcoeff : (max (C * C) 40) ^ 2 ≤ δ ^ (-4 * κ) := by
    calc (max (C * C) 40) ^ 2 ≤ (δ ^ (-2 * κ)) ^ 2 := by gcongr; exact max_le hCC hforty
      _ = _ := by rw [pow_two, ← Real.rpow_add hδ]; congr 1; ring
  have h16 : (1 / 16 : ℝ) ≤ 16 ^ (2500 * κ - 1) := by
    calc (1 / 16 : ℝ) = 16 ^ (-1 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlower : δ ^ ((1 - 200 * κ) * (2500 * κ - 1)) / 16 ≤
      (16 * δ / (δ ^ (100 * κ) * δ ^ (100 * κ))) ^ (2500 * κ - 1) := by
    rw [ring_ratio_scale hδ, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ.le]
    nlinarith [mul_le_mul_of_nonneg_right h16
      (Real.rpow_nonneg hδ.le ((1 - 200 * κ) * (2500 * κ - 1)))]
  have hcount' : δ ^ a ≤ 16 * N := by
    have hh := hlower.trans (hcount.trans (mul_le_mul_of_nonneg_right hcoeff hN))
    have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hδ.le (4 * κ))
    have hid : δ ^ (-4 * κ) * δ ^ (4 * κ) = 1 := by rw [← Real.rpow_add hδ]; simp
    have hid' : δ ^ ((1 - 200 * κ) * (2500 * κ - 1)) * δ ^ (4 * κ) = δ ^ a := by
      rw [← Real.rpow_add hδ]
    nlinarith [hm]
  have hpower : δ ^ (-σ - 10 * κ - a) ≤ δ ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [a]; nlinarith [sq_nonneg κ])
  have hc : 16 * δ ^ (-σ - 10 * κ - a) ≤ 1 := by
    have := Real.rpow_pos_of_pos hδ κ
    nlinarith
  have hlow : 16 * δ ^ (-σ - 10 * κ) ≤ δ ^ a := by
    calc
      16 * δ ^ (-σ - 10 * κ) = (16 * δ ^ (-σ - 10 * κ - a)) * δ ^ a := by
        rw [mul_assoc, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ 1 * δ ^ a := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hδ.le a)
      _ = _ := one_mul _
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
