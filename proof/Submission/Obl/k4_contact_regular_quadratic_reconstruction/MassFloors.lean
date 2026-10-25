import Mathlib

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction

open scoped ENNReal

/-- On a bounded depth horizon, a candidate's original assignment-relative
floor is bounded below by one fixed inverse power. -/
theorem original_candidate_power_floor
    {N K d κ s v ε U : ℝ} {T : ℕ} {prior mass : ℝ≥0∞}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hKN : K ≤ N)
    (_hd0 : 0 ≤ d) (hd1 : d ≤ 1) (_hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hsv : s + v ≤ U) (hε : ε ≤ 1)
    (htime : (2 : ℝ) ^ T ≤ K * N ^ (κ * s))
    (hprior : ENNReal.ofReal
      ((N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ (2 : ℕ) * N ^ (-κ * s) / K) ≤ prior)
    (hmass : ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * prior ≤ mass) :
    ENNReal.ofReal (N ^ (-(5 * U + 5))) ≤ mass := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hK0 : 0 < K := by linarith
  have htime' : (2 : ℝ) ^ T ≤ N ^ (κ * s + 1) := by
    calc
      (2 : ℝ) ^ T ≤ K * N ^ (κ * s) := htime
      _ ≤ N * N ^ (κ * s) := mul_le_mul_of_nonneg_right hKN (by positivity)
      _ = _ := by rw [Real.rpow_add hN0, Real.rpow_one]; ring
  have hq : N ^ (-κ * s - 1) ≤ ((2 : ℝ) ^ T)⁻¹ := by
    have hh := inv_anti₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ T) htime'
    rw [← Real.rpow_neg hN0.le] at hh
    simpa only [show -(κ * s + 1) = -κ * s - 1 by ring] using hh
  have hinv : N ^ (-1 : ℝ) ≤ K⁻¹ := by
    rw [Real.rpow_neg_one]
    exact inv_anti₀ hK0 hKN
  have hdsum : d * (s + v) ≤ U := by
    calc
      d * (s + v) ≤ 1 * (s + v) := mul_le_mul_of_nonneg_right hd1 (by positivity)
      _ ≤ U := by simpa only [one_mul] using hsv
  have hks : κ * s ≤ U := by
    calc
      κ * s ≤ 1 * s := mul_le_mul_of_nonneg_right hκ1 hs
      _ ≤ U := by linarith
  have hexp : -(5 * U + 5) ≤ -d * (s + v) - 4 * κ * s - ε - 4 := by
    linarith
  have hcanonical :
      N ^ (-d * v - ε) * N ^ (-κ * s - 1) *
        ((N ^ (-s)) ^ d * (N ^ (-κ * s - 1)) ^ (2 : ℕ) *
          N ^ (-κ * s) * N ^ (-1 : ℝ)) =
        N ^ (-d * (s + v) - 4 * κ * s - ε - 4) := by
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    simp only [← Real.rpow_add hN0]
    congr 1
    norm_num
    ring
  have hreal : N ^ (-(5 * U + 5)) ≤
      (N ^ (-d * v - ε) / (2 : ℝ) ^ T) *
        ((N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ (2 : ℕ) * N ^ (-κ * s) / K) := by
    calc
      _ ≤ N ^ (-d * (s + v) - 4 * κ * s - ε - 4) :=
        Real.rpow_le_rpow_of_exponent_le hN1 hexp
      _ = N ^ (-d * v - ε) * N ^ (-κ * s - 1) *
          ((N ^ (-s)) ^ d * (N ^ (-κ * s - 1)) ^ (2 : ℕ) *
            N ^ (-κ * s) * N ^ (-1 : ℝ)) := hcanonical.symm
      _ ≤ _ := by
        simp only [div_eq_mul_inv]
        gcongr
  have hweight : 0 ≤ N ^ (-d * v - ε) / (2 : ℝ) ^ T := by positivity
  calc
    ENNReal.ofReal (N ^ (-(5 * U + 5))) ≤
        ENNReal.ofReal ((N ^ (-d * v - ε) / (2 : ℝ) ^ T) *
          ((N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ (2 : ℕ) * N ^ (-κ * s) / K)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) *
        ENNReal.ofReal ((N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ (2 : ℕ) * N ^ (-κ * s) / K) :=
      ENNReal.ofReal_mul hweight
    _ ≤ ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * prior :=
      mul_le_mul_right hprior _
    _ ≤ mass := hmass

/-- A fixed fraction of the real canonical source floor still has a fixed
power lower bound. This pays for the quarter-band witness selection before
native calibration, in the original mass units. -/
theorem retained_original_reference_power_floor
    {N K d κ s v ε U : ℝ} {T : ℕ}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hKN : K ≤ N)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hsv : s + v ≤ U) (hε : ε ≤ 1)
    (htime : (2 : ℝ) ^ T ≤ K * N ^ (κ * s)) :
    N ^ (-(5 * U + 10)) ≤
      N ^ (-d * v - ε) * ((2 : ℝ) ^ T)⁻¹ *
        ((N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ (2 : ℕ) * N ^ (-κ * s) / K) / 18 := by
  have hN0 : 0 < N := by linarith only [hN]
  have hK0 : 0 < K := by linarith only [hK]
  let prior : ℝ :=
    (N ^ (-s)) ^ d * ((2 : ℝ) ^ T)⁻¹ ^ (2 : ℕ) * N ^ (-κ * s) / K
  let mass : ℝ := (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * prior
  have hweight : 0 ≤ N ^ (-d * v - ε) / (2 : ℝ) ^ T := by positivity
  have hmass0 : 0 ≤ mass := by dsimp [mass, prior]; positivity
  have hfloor : ENNReal.ofReal (N ^ (-(5 * U + 5))) ≤ ENNReal.ofReal mass := by
    apply original_candidate_power_floor (prior := ENNReal.ofReal prior)
      hN hK hKN hd0 hd1 hκ0 hκ1 hs hv hsv hε htime le_rfl
    dsimp [mass]
    rw [ENNReal.ofReal_mul hweight]
  have hreal : N ^ (-(5 * U + 5)) ≤ mass :=
    (ENNReal.ofReal_le_ofReal_iff hmass0).mp hfloor
  have hpow : (18 : ℝ) ≤ N ^ (5 : ℕ) := by
    calc
      (18 : ℝ) ≤ 2 ^ (5 : ℕ) := by norm_num
      _ ≤ N ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hN 5
  have hinv : N ^ (-5 : ℝ) ≤ (1 : ℝ) / 18 := by
    rw [Real.rpow_neg hN0.le, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 18) hpow
  have hretained : N ^ (-(5 * U + 10)) ≤ mass / 18 := by
    calc
      _ = N ^ (-(5 * U + 5)) * N ^ (-5 : ℝ) := by
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      _ ≤ mass * ((1 : ℝ) / 18) := mul_le_mul hreal hinv (by positivity) hmass0
      _ = mass / 18 := by ring
  simpa only [mass, prior, div_eq_mul_inv] using hretained

end Submission.Obl.k4_contact_regular_quadratic_reconstruction
