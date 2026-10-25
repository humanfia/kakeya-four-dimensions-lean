/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/ShortSegments.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156, session x0524 branch c7cfd90,
Submission/Obl/k4_terminal_local_sheet_pairing/ShortSegments.lean. Original authorship/provenance is preserved below.
Namespace and imports adjusted for o114. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SimpleSheets

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set

/-- Endpoint bounds control the slope of an affine hidden derivative. -/
theorem affine_slope_bound {m d s e V : ℝ} (hse : s < e)
    (hs : |m * s + d| ≤ V) (he : |m * e + d| ≤ V) :
    |m| ≤ 2 * V / (e - s) := by
  apply (le_div_iff₀ (sub_pos.mpr hse)).mpr
  calc
    |m| * (e - s) = |m * (e - s)| := by rw [abs_mul, abs_of_pos (sub_pos.mpr hse)]
    _ = |(m * e + d) - (m * s + d)| := by congr 1; ring
    _ ≤ |m * e + d| + |m * s + d| := abs_sub _ _
    _ ≤ 2 * V := by linarith

/-- A small derivative change preserves the source branch sign and a half floor. -/
theorem derivative_sign_persists {d₀ d σ B : ℝ} (hB : 0 < B) (hσ : σ ^ 2 = 1)
    (hsign : σ * d₀ = |d₀|) (hfloor : B ≤ |d₀|) (hchange : |d - d₀| ≤ B / 2) :
    B / 2 ≤ |d| ∧ σ * d = |d| := by
  have hσabs : |σ| = 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have hlo := neg_abs_le (σ * (d - d₀))
  rw [abs_mul, hσabs, one_mul] at hlo
  have hpos : 0 < σ * d := by nlinarith
  have hsign' : σ * d = |d| := by
    calc
      σ * d = |σ * d| := (abs_of_pos hpos).symm
      _ = |d| := by rw [abs_mul, hσabs, one_mul]
  exact ⟨by rw [← hsign']; nlinarith, hsign'⟩

/-- The same branch fits a short segment of an actual trajectory. The only
time-dependent input to the branch choice is the affine hidden derivative. -/
theorem quadratic_short_segment_fit {a b w : ℝ → ℝ} {c m d s e t₀ V B ρ r : ℝ}
    (hc : c ≠ 0) (hse : s < e) (hV : 0 ≤ V) (hB : 0 < B) (hρ : 0 ≤ ρ)
    (hs : |m * s + d| ≤ V) (he : |m * e + d| ≤ V)
    (hfloor : B ≤ |m * t₀ + d|)
    (hsmall : (2 * V / (e - s)) * r ≤ B / 2)
    (hderiv : ∀ t ∈ Icc s e, b t + 2 * c * w t = m * t + d)
    (hdisc : ∀ t ∈ Icc s e, 0 ≤ b t ^ 2 - 4 * c * a t)
    (hres : ∀ t ∈ Icc s e, |a t + b t * w t + c * w t ^ 2| ≤ ρ) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧
      ∀ t ∈ Icc s e ∩ Icc (t₀ - r) (t₀ + r),
        |w t - (-b t + σ * Real.sqrt (b t ^ 2 - 4 * c * a t)) / (2 * c)| ≤ 4 * ρ / B := by
  let σ : ℝ := if 0 ≤ m * t₀ + d then 1 else -1
  have hσ : σ ^ 2 = 1 := by dsimp [σ]; split_ifs <;> norm_num
  have hsign : σ * (m * t₀ + d) = |m * t₀ + d| := by
    dsimp [σ]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  refine ⟨σ, hσ, fun t ht => ?_⟩
  have hdist : |t - t₀| ≤ r := abs_le.mpr ⟨by linarith [ht.2.1], by linarith [ht.2.2]⟩
  have hchange : |(m * t + d) - (m * t₀ + d)| ≤ B / 2 := by
    calc
      |(m * t + d) - (m * t₀ + d)| = |m| * |t - t₀| := by rw [← abs_mul]; congr 1; ring
      _ ≤ (2 * V / (e - s)) * r :=
        mul_le_mul (affine_slope_bound hse hs he) hdist (abs_nonneg _) (by positivity)
      _ ≤ B / 2 := hsmall
  obtain ⟨hBt, hsignt⟩ := derivative_sign_persists hB hσ hsign hfloor hchange
  have hne : b t + 2 * c * w t ≠ 0 := by
    rw [hderiv t ht.1]
    intro hzero
    simp only [hzero, abs_zero] at hBt
    linarith
  have herr := quadraticBranch_error hc hσ (hdisc t ht.1) hne
    (by rw [hderiv t ht.1]; exact hsignt)
  refine herr.trans ?_
  rw [hderiv t ht.1]
  calc
    2 * |a t + b t * w t + c * w t ^ 2| / |m * t + d| ≤ 2 * ρ / (B / 2) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hres t ht.1) (by norm_num))
        (by positivity) hBt
    _ = 4 * ρ / B := by ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
