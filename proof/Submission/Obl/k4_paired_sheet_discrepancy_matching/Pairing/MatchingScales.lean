/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/MatchingScales.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Mathlib

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

/-- Fixed exponents chosen before the tested problem and its complexity. -/
structure MatchingScales (d₀ ε₀ : ℝ) where
  middle : ℝ
  slack : ℝ
  size : ℝ
  middle_nonneg : 0 ≤ middle
  middle_gt : d₀ < middle
  slack_pos : 0 < slack
  slack_le : slack ≤ ε₀
  sum_le_one : middle + slack ≤ 1
  size_one : 1 ≤ size
  density_gap : 10 ≤ size * slack
  counting_gap : 12 ≤ size * (middle - d₀)

theorem matchingScales_at_middle {d₀ d ε₀ : ℝ} (hd : d₀ < d) (hd0 : 0 ≤ d)
    (hd1 : d < 1) (hε₀ : 0 < ε₀) : ∃ p : MatchingScales d₀ ε₀, p.middle = d := by
  let ε := min ε₀ ((1 - d) / 2)
  have hε : 0 < ε := lt_min hε₀ (by linarith)
  let T := max 1 (max (10 / ε) (12 / (d - d₀)))
  have hTε : 10 ≤ T * ε := by
    have hle : 10 / ε ≤ T := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hε).mp hle
  have hTd : 12 ≤ T * (d - d₀) := by
    have hle : 12 / (d - d₀) ≤ T := (le_max_right _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ (sub_pos.mpr hd)).mp hle
  refine ⟨⟨d, ε, T, hd0, hd, hε, min_le_left _ _, ?_, le_max_left _ _, hTε, hTd⟩, rfl⟩
  have := min_le_right ε₀ ((1 - d) / 2)
  change d + min ε₀ ((1 - d) / 2) ≤ 1
  linarith

theorem matchingScales_nonempty {d₀ ε₀ : ℝ} (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1)
    (hε₀ : 0 < ε₀) : Nonempty (MatchingScales d₀ ε₀) := by
  let d := (1 + d₀) / 2
  let ε := min ε₀ ((1 - d₀) / 4)
  have hd : d₀ < d := by dsimp [d]; linarith
  have hε : 0 < ε := lt_min hε₀ (by linarith)
  let T := max 1 (max (10 / ε) (12 / (d - d₀)))
  have hTε : 10 ≤ T * ε := by
    have hle : 10 / ε ≤ T := (le_max_left _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ hε).mp hle
  have hTd : 12 ≤ T * (d - d₀) := by
    have hle : 12 / (d - d₀) ≤ T := (le_max_right _ _).trans (le_max_right _ _)
    exact (div_le_iff₀ (sub_pos.mpr hd)).mp hle
  refine ⟨⟨d, ε, T, ?_, hd, hε, min_le_left _ _, ?_, le_max_left _ _, hTε, hTd⟩⟩
  · dsimp [d]
    linarith
  · have := min_le_right ε₀ ((1 - d₀) / 4)
    dsimp [d]
    linarith

namespace MatchingScales

variable {d₀ ε₀ : ℝ} (p : MatchingScales d₀ ε₀)

noncomputable def decay : ℝ := (2 : ℝ) ^ (-p.slack / 2)
def output : ℝ := p.size + 4

theorem decay_pos : 0 < p.decay := Real.rpow_pos_of_pos (by norm_num) _

theorem decay_lt_one : p.decay < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by have := p.slack_pos; linarith)

theorem density_growth : (2 : ℝ) ^ (-p.slack) ≤ p.decay :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have := p.slack_pos; linarith)

theorem band_growth {d : ℝ} (hd : d ≤ d₀) :
    (2 : ℝ) ^ d ≤ p.decay * (2 : ℝ) ^ (p.middle + p.slack) := by
  rw [decay, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := p.middle_gt
  have := p.slack_pos
  linarith

theorem density_base {X ρ τ : ℝ} (hX : 4 ≤ X) (hρ : 0 ≤ ρ) (hτ : 0 < τ) :
    ρ * (X ^ p.size) ^ (-p.slack) ≤ (ρ + τ) * X ^ (-8 : ℝ) / 2 := by
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hpow : (X ^ p.size) ^ (-p.slack) ≤ X ^ (-10 : ℝ) := by
    rw [← Real.rpow_mul hXpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hXone
    have := p.density_gap
    nlinarith
  have hinv : X ^ (-2 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hXpos.le, Real.rpow_two]
    have hh : (2 : ℝ) ≤ X ^ 2 := by nlinarith
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hh
  have hsmall : X ^ (-10 : ℝ) ≤ X ^ (-8 : ℝ) / 2 := by
    rw [show (-10 : ℝ) = -8 + -2 by norm_num, Real.rpow_add hXpos]
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hXpos.le (-8))
  calc _ ≤ ρ * (X ^ (-8 : ℝ) / 2) := mul_le_mul_of_nonneg_left (hpow.trans hsmall) hρ
    _ ≤ (ρ + τ) * (X ^ (-8 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

theorem band_base {X ρ τ K Y d : ℝ} (hX : 4 ≤ X)
    (hρ : 0 ≤ ρ) (hτ : 0 < τ) (hK : 0 ≤ K) (hKX : K ≤ X)
    (hY : 0 ≤ Y) (hYX : Y ≤ X ^ (p.size + 3)) (hd : 0 ≤ d) (hdd : d ≤ d₀) :
    (K * ρ * Y ^ d) / ((ρ + τ) * X ^ (-8 : ℝ)) ≤
      (X ^ p.size) ^ (p.middle + p.slack) := by
  have hXpos : 0 < X := by linarith
  have hXone : 1 ≤ X := by linarith
  have hcancel : X ^ (8 : ℝ) * X ^ (-8 : ℝ) = 1 := by
    rw [← Real.rpow_add hXpos]
    norm_num
  have hratio : (K * ρ * Y ^ d) / ((ρ + τ) * X ^ (-8 : ℝ)) ≤
      K * X ^ (8 : ℝ) * Y ^ d := by
    apply (div_le_iff₀ (by positivity : 0 < (ρ + τ) * X ^ (-8 : ℝ))).mpr
    calc _ ≤ K * (ρ + τ) * Y ^ d := by gcongr; linarith
      _ = K * (ρ + τ) * Y ^ d * (X ^ (8 : ℝ) * X ^ (-8 : ℝ)) := by rw [hcancel, mul_one]
      _ = _ := by ring
  have hsize : 0 ≤ p.size := zero_le_one.trans p.size_one
  have hdc : d ≤ 1 := by have := p.middle_gt; have := p.sum_le_one; have := p.slack_pos; linarith
  have hexp : 9 + (p.size + 3) * d ≤ p.size * (p.middle + p.slack) := by
    have hgap := p.counting_gap
    have hleft := mul_nonneg hsize (sub_nonneg.mpr hdd)
    have hright := mul_nonneg hsize p.slack_pos.le
    nlinarith
  calc _ ≤ K * X ^ (8 : ℝ) * Y ^ d := hratio
    _ ≤ X * X ^ (8 : ℝ) * (X ^ (p.size + 3)) ^ d := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hKX (Real.rpow_nonneg hXpos.le _)
      · exact Real.rpow_le_rpow hY hYX hd
      · exact Real.rpow_nonneg hY d
      · positivity
    _ = X ^ (9 + (p.size + 3) * d) := by
      rw [← Real.rpow_mul hXpos.le]
      have hX8 : X * X ^ (8 : ℝ) = X ^ (9 : ℝ) := by
        calc _ = X ^ (1 : ℝ) * X ^ (8 : ℝ) := by rw [Real.rpow_one]
          _ = X ^ ((1 : ℝ) + 8) := (Real.rpow_add hXpos _ _).symm
          _ = _ := by norm_num
      rw [hX8, ← Real.rpow_add hXpos]
    _ ≤ X ^ (p.size * (p.middle + p.slack)) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexp
    _ = _ := Real.rpow_mul hXpos.le _ _

end MatchingScales

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
