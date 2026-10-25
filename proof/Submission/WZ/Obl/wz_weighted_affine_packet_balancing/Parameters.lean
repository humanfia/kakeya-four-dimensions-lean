-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_weighted_affine_packet_balancing.Parameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_weighted_affine_packet_balancing

/-- A fixed number of multiplicative bins costs less than the exponent slack. -/
theorem parameters (e : ℝ) (he : 0 < e) :
    ∃ (s : ℝ) (b : ℕ) (d₀ : ℝ), 0 < s ∧ 0 < b ∧ 0 < d₀ ∧
      d₀ ≤ (1 / 100 : ℝ) ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      d ^ e ≤ d ^ s ∧ 1 < d ^ (-s) ∧ d ^ (-100 : ℝ) < (d ^ (-s)) ^ b ∧
      d ^ e * ((b : ℝ) * d ^ (-s)) ≤ d ^ s ∧ 2 * (d ^ e) ^ 2 ≤ 1 := by
  let s : ℝ := e / 4
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨b, hb⟩ := exists_nat_gt (100 / s)
  have hbpos : 0 < b := by
    have : 0 < (b : ℝ) := lt_trans (by positivity) hb
    exact_mod_cast this
  have hsb : 100 < s * b := by
    have := (div_lt_iff₀ hs).mp hb
    nlinarith
  let C : ℝ := 2 * (b : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  let D : ℝ := (1 / C) ^ (1 / (e / 2))
  have hD : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨s, b, min (1 / 100) D, hs, hbpos,
    lt_min (by norm_num) hD, min_le_left _ _, ?_⟩
  intro d hd hdd
  have hd1 : d ≤ 1 := (hdd.trans (min_le_left _ _)).trans (by norm_num)
  have hdlt : d < 1 := (hdd.trans (min_le_left _ _)).trans_lt (by norm_num)
  have hsmall : d ^ (e / 2) ≤ 1 / C := by
    calc
      d ^ (e / 2) ≤ D ^ (e / 2) :=
        Real.rpow_le_rpow hd.le (hdd.trans (min_le_right _ _)) (by positivity)
      _ = 1 / C := by
        dsimp [D]
        rw [one_div (e / 2), Real.rpow_inv_rpow (by positivity) (by positivity)]
  have hbin : d ^ (e / 2) * (b : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg b)
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have hc : 1 / C * (b : ℝ) = 1 / 2 := by dsimp [C]; field_simp
    rw [hc] at h
    linarith
  have hhalf : d ^ e ≤ 1 / 2 := by
    have hh : d ^ e ≤ d ^ (e / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hbpos
    have hh' : 1 / C ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      dsimp [C]
      linarith
    exact hh.trans (hsmall.trans hh')
  refine ⟨Real.rpow_le_rpow_of_exponent_ge hd hd1 (by dsimp [s]; linarith),
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg hd hdlt (by linarith), ?_, ?_, ?_⟩
  · rw [← Real.rpow_mul_natCast hd.le]
    exact Real.rpow_lt_rpow_of_exponent_gt hd hdlt (by nlinarith)
  · have hid : d ^ e * ((b : ℝ) * d ^ (-s)) =
        d ^ s * (d ^ (e / 2) * b) := by
      calc
        _ = (b : ℝ) * d ^ (e - s) := by
          rw [Real.rpow_sub hd]
          rw [Real.rpow_neg hd.le]
          ring
        _ = d ^ s * (d ^ (e / 2) * b) := by
          rw [← mul_assoc, ← Real.rpow_add hd]
          have : s + e / 2 = e - s := by dsimp [s]; ring
          rw [this]
          ring
    rw [hid]
    simpa using mul_le_mul_of_nonneg_left hbin (Real.rpow_nonneg hd.le s)
  · have hn := Real.rpow_nonneg hd.le e
    nlinarith

end WangZahlLot.Obl.wz_weighted_affine_packet_balancing
