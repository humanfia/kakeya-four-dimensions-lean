import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.BlockCover

/-!
# Numerical bounds for the cover constants

Plain real inequalities for `K ≥ 1`, `0 < H ≤ 1`, `0 < p₀ ≤ 1`, `0 ≤ d < 1`:
`cnt1 ≤ 24 K³ p₀^(-d)`, `cap2 ≤ 63 K² H^d p₀^(2+d)`, their product `≤ 1512 K⁵ H^d p₀²`,
`groupMass ≤ 144 K⁴ H^d`, `groupCount ≤ 70 K⁴ H^(-d)`, `slopeVar ≤ (8K² + 2KA) p₀`, and a bound
for `pairBound`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

theorem rpow_le_self_of_one_le {x d : ℝ} (hx : 1 ≤ x) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    x ^ d ≤ x := by
  calc x ^ d ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hd1
    _ = x := Real.rpow_one x

theorem cnt1_le {K d p₀ : ℝ} (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd1 : d < 1) (hp₀ : 0 < p₀) :
    cnt1 K d p₀ ≤ 24 * K ^ 3 * p₀ ^ (-d) := by
  unfold cnt1
  have hb : 1 ≤ 2 * (4 * K ^ 2 + K + 1) := by nlinarith
  have h1 : (2 * (4 * K ^ 2 + K + 1) / p₀) ^ d = (2 * (4 * K ^ 2 + K + 1)) ^ d * p₀ ^ (-d) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hp₀.le,
      Real.rpow_neg hp₀.le]
  rw [h1]
  have h2 : (2 * (4 * K ^ 2 + K + 1)) ^ d ≤ 12 * K ^ 2 := by
    refine (rpow_le_self_of_one_le hb hd0 hd1.le).trans ?_
    nlinarith
  have hp : 0 ≤ p₀ ^ (-d) := Real.rpow_nonneg hp₀.le _
  calc 2 * (K * ((2 * (4 * K ^ 2 + K + 1)) ^ d * p₀ ^ (-d)))
      ≤ 2 * (K * (12 * K ^ 2 * p₀ ^ (-d))) := by gcongr
    _ = 24 * K ^ 3 * p₀ ^ (-d) := by ring

theorem cap2_le {K d H p₀ : ℝ} (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hH : 0 < H) (hH1 : H ≤ 1)
    (hp₀ : 0 < p₀) : cap2 K d H p₀ ≤ 63 * K ^ 2 * H ^ d * p₀ ^ (2 + d) := by
  unfold cap2
  have h1 : (1 / H + 2) ^ 2 ≤ 9 / H ^ 2 := by
    have : 1 / H + 2 ≤ 3 / H := by
      rw [div_add' _ _ _ hH.ne', div_le_div_iff_of_pos_right hH]; linarith
    calc (1 / H + 2) ^ 2 ≤ (3 / H) ^ 2 := by gcongr
      _ = 9 / H ^ 2 := by ring
  have h2 : (H * p₀) ^ (2 + d) = H ^ 2 * H ^ d * p₀ ^ (2 + d) := by
    rw [Real.mul_rpow hH.le hp₀.le, Real.rpow_add hH, Real.rpow_two]
  rw [h2]
  have hHd : 0 ≤ H ^ d := Real.rpow_nonneg hH.le _
  have hp : 0 ≤ p₀ ^ (2 + d) := Real.rpow_nonneg hp₀.le _
  calc (1 / H + 2) ^ 2 * (4 * K + 3) * (K * (H ^ 2 * H ^ d * p₀ ^ (2 + d)))
      ≤ 9 / H ^ 2 * (7 * K) * (K * (H ^ 2 * H ^ d * p₀ ^ (2 + d))) := by
        gcongr; linarith
    _ = 63 * K ^ 2 * H ^ d * p₀ ^ (2 + d) := by field_simp; ring

theorem cnt1_cap2_le {K d H p₀ : ℝ} (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hd1 : d < 1) (hH : 0 < H)
    (hH1 : H ≤ 1) (hp₀ : 0 < p₀) :
    cnt1 K d p₀ * cap2 K d H p₀ ≤ 1512 * K ^ 5 * H ^ d * p₀ ^ 2 := by
  have h1 := cnt1_le hK hd0 hd1 hp₀
  have h2 := cap2_le hK hd0 hH hH1 hp₀
  have hc : 0 ≤ cap2 K d H p₀ := by unfold cap2; positivity
  have e : p₀ ^ (-d) * p₀ ^ (2 + d) = p₀ ^ 2 := by
    rw [← Real.rpow_add hp₀]; norm_num
  calc cnt1 K d p₀ * cap2 K d H p₀ ≤ 24 * K ^ 3 * p₀ ^ (-d) * (63 * K ^ 2 * H ^ d * p₀ ^ (2 + d)) :=
        mul_le_mul h1 h2 hc (by positivity)
    _ = 1512 * K ^ 5 * H ^ d * (p₀ ^ (-d) * p₀ ^ (2 + d)) := by ring
    _ = 1512 * K ^ 5 * H ^ d * p₀ ^ 2 := by rw [e]

theorem groupMass_le {K d H : ℝ} (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hH : 0 < H) (hH1 : H ≤ 1) :
    groupMass K d H ≤ 144 * K ^ 4 * H ^ d := by
  unfold groupMass
  have h1 : (2 * K / H + 2) ^ 2 ≤ 16 * K ^ 2 / H ^ 2 := by
    have : 2 * K / H + 2 ≤ 4 * K / H := by
      rw [div_add' _ _ _ hH.ne', div_le_div_iff_of_pos_right hH]; nlinarith
    calc (2 * K / H + 2) ^ 2 ≤ (4 * K / H) ^ 2 := by gcongr
      _ = 16 * K ^ 2 / H ^ 2 := by ring
  have h2 : H ^ (2 + d) = H ^ 2 * H ^ d := by rw [Real.rpow_add hH, Real.rpow_two]
  rw [h2]
  have hHd : 0 ≤ H ^ d := Real.rpow_nonneg hH.le _
  calc (2 * K / H + 2) ^ 2 * (2 * K + 1 + 4 * K + 2) * (K * (H ^ 2 * H ^ d))
      ≤ 16 * K ^ 2 / H ^ 2 * (9 * K) * (K * (H ^ 2 * H ^ d)) := by
        gcongr; linarith
    _ = 144 * K ^ 4 * H ^ d := by field_simp; ring

theorem groupCount_le {K d H : ℝ} (hK : 1 ≤ K) (hd0 : 0 ≤ d) (hH : 0 < H) :
    groupCount K d H ≤ 70 * K ^ 4 * (1 / H) ^ d := by
  unfold groupCount
  have h1 : 2 * (2 * K + 2 * K ^ 2) + 2 ≤ 10 * K ^ 2 := by nlinarith
  have h2 : (2 * (⌈K⌉₊ : ℝ) + 3) ≤ 7 * K := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ K by linarith)
    linarith
  have hHd : 0 ≤ (1 / H) ^ d := Real.rpow_nonneg (by positivity) _
  calc (2 * (2 * K + 2 * K ^ 2) + 2) * (K * (1 / H) ^ d) * (2 * ⌈K⌉₊ + 3)
      ≤ 10 * K ^ 2 * (K * (1 / H) ^ d) * (7 * K) := by gcongr
    _ = 70 * K ^ 4 * (1 / H) ^ d := by ring

theorem slopeVar_le {K KA H p₀ ζ : ℝ} (hK : 1 ≤ K) (hKA : 0 ≤ KA) (hζ0 : 0 ≤ ζ)
    (hζH : ζ ≤ H) (hHp : H ≤ p₀) : slopeVar K KA H p₀ ζ ≤ (8 * K ^ 2 + 2 * KA) * p₀ := by
  unfold slopeVar
  have hp₀ : 0 ≤ p₀ := (hζ0.trans hζH).trans hHp
  have : H * (1 + 2 * K) + 2 * K * p₀ + 2 * p₀ + ζ ≤ 8 * K * p₀ := by nlinarith
  nlinarith

theorem pairBound_le {K KA d w mL : ℝ} (hK : 1 ≤ K) (hKA : 0 ≤ KA) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hw : 0 < w) (hmL : 0 < mL) :
    pairBound K KA d w mL ≤ 13970880 * K ^ 10 * (4 * KA + 5) / mL ^ 2 * (1 / w) ^ d := by
  unfold pairBound
  have h1 : 2 * (2 * K + 2 * K ^ 2) + 2 ≤ 10 * K ^ 2 := by nlinarith
  have hc : (⌈K⌉₊ : ℝ) ≤ K + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have h2 : (K * (2 * ⌈K⌉₊ + 3)) ^ 2 ≤ 49 * K ^ 4 := by
    have : K * (2 * ⌈K⌉₊ + 3) ≤ 7 * K ^ 2 := by nlinarith
    calc (K * (2 * ⌈K⌉₊ + 3)) ^ 2 ≤ (7 * K ^ 2) ^ 2 := by gcongr
      _ = 49 * K ^ 4 := by ring
  have h3 : 9 * (6 * K + 3) * K * (2 : ℝ) ^ d ≤ 162 * K ^ 2 := by
    have : (2 : ℝ) ^ d ≤ 2 := rpow_le_self_of_one_le (by norm_num) hd0 hd1.le
    have : 9 * (6 * K + 3) * K ≤ 81 * K ^ 2 := by nlinarith
    nlinarith
  have h4 : ((⌈4 * KA + 4⌉₊ * ⌈4 * K + 6⌉₊ : ℕ) : ℝ) ≤ (4 * KA + 5) * (11 * K) := by
    push_cast
    have a1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * KA + 4 by positivity)).le
    have a2 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * K + 6 by linarith)).le
    have : 4 * K + 6 + 1 ≤ 11 * K := by linarith
    exact mul_le_mul (by linarith) (a2.trans this) (Nat.cast_nonneg _) (by positivity)
  have hw' : 0 ≤ (1 / w) ^ d := Real.rpow_nonneg (by positivity) _
  have e : (4 / mL) ^ 2 = 16 / mL ^ 2 := by ring
  rw [e]
  calc (2 * (2 * K + 2 * K ^ 2) + 2) * (K * (1 / w) ^ d) * (K * (2 * ⌈K⌉₊ + 3)) ^ 2 *
        (9 * (6 * K + 3) * K * 2 ^ d) * ((⌈4 * KA + 4⌉₊ * ⌈4 * K + 6⌉₊ : ℕ) : ℝ) * (16 / mL ^ 2)
      ≤ 10 * K ^ 2 * (K * (1 / w) ^ d) * (49 * K ^ 4) * (162 * K ^ 2) *
        ((4 * KA + 5) * (11 * K)) * (16 / mL ^ 2) := by
        gcongr
    _ = 13970880 * K ^ 10 * (4 * KA + 5) / mL ^ 2 * (1 / w) ^ d := by ring

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
