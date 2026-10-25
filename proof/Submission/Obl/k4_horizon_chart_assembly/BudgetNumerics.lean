import Submission.Obl.k4_horizon_chart_assembly.ParameterScales

namespace Submission.Obl.k4_horizon_chart_assembly

/-- The threshold inverse has a fixed polynomial cost, independently of the
later tolerance exponent, when the slack is at most the base scale. -/
theorem atlas_threshold_inverse_bound {N K q L f κ : ℝ}
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hq : N ^ (-L) / 8 ≤ q)
    (hκ : 0 < κ) (hκN : κ ≤ N) :
    (4 * N ^ (-f) * ((2 * K + 2) * q) ^ 2 / κ)⁻¹ ≤
      16 * N ^ (1 + f + 2 * L) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hq₀ : 0 < q := lt_of_lt_of_le (by positivity) hq
  have hR : 1 ≤ 2 * K + 2 := by linarith
  have hqpow : N ^ (-2 * L) / 64 ≤ ((2 * K + 2) * q) ^ 2 := by
    have hRq : q ≤ (2 * K + 2) * q := by nlinarith
    have hsq : (N ^ (-L) / 8) ^ 2 ≤ ((2 * K + 2) * q) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hq.trans hRq) 2
    have heq : (N ^ (-L) / 8) ^ 2 = N ^ (-2 * L) / 64 := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN₀.le]
      norm_num
      congr 2
      ring
    rwa [heq] at hsq
  have hden : 0 < 4 * N ^ (-f) * ((2 * K + 2) * q) ^ 2 := by positivity
  have hbound : 0 < N ^ (-(f + 2 * L)) / 16 := by positivity
  have hlower : N ^ (-(f + 2 * L)) / 16 ≤
      4 * N ^ (-f) * ((2 * K + 2) * q) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hqpow (show 0 ≤ 4 * N ^ (-f) by positivity)
    have heq : 4 * N ^ (-f) * (N ^ (-2 * L) / 64) =
        N ^ (-(f + 2 * L)) / 16 := by
      rw [show -(f + 2 * L) = -f + -2 * L by ring, Real.rpow_add hN₀]
      ring
    simpa only [heq] using hm
  calc
    _ = κ / (4 * N ^ (-f) * ((2 * K + 2) * q) ^ 2) := by rw [inv_div]
    _ ≤ N / (N ^ (-(f + 2 * L)) / 16) :=
      (div_le_div_iff₀ hden hbound).2
        ((mul_le_mul_of_nonneg_right hκN hbound.le).trans
          (mul_le_mul_of_nonneg_left hlower hN₀.le))
    _ = 16 * N ^ (1 + f + 2 * L) := by
      rw [div_div_eq_mul_div, Real.rpow_neg hN₀.le, div_inv_eq_mul]
      simp only [show 1 + f + 2 * L = 1 + (f + 2 * L) by ring,
        Real.rpow_add hN₀, Real.rpow_one]
      ring

/-- Six polynomially bounded numerical inputs fit in one fixed integer power.
This is the complexity envelope used before any tolerance is chosen. -/
theorem atlas_six_term_budget {N H K D t τ : ℝ} {p C : ℕ}
    (hN : 2 ≤ N) (hH : H ≤ N ^ p) (hK : K ≤ N ^ p)
    (hD : D ≤ N ^ p) (ht : t ≤ N ^ p) (hτ : τ⁻¹ ≤ N ^ p)
    (hV : 0 ≤ 1 + H + K + D + t + τ⁻¹) :
    (1 + H + K + D + t + τ⁻¹) ^ C ≤ N ^ ((p + 3) * C) := by
  have hN₁ : 1 ≤ N := by linarith
  have hbase : 1 ≤ N ^ p := one_le_pow₀ hN₁
  have hthree : (6 : ℝ) ≤ N ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3]
  have hsum : 1 + H + K + D + t + τ⁻¹ ≤ N ^ (p + 3) := by
    calc
      _ ≤ 6 * N ^ p := by linarith
      _ ≤ N ^ 3 * N ^ p := mul_le_mul_of_nonneg_right hthree (by positivity)
      _ = N ^ (p + 3) := by rw [pow_add]; ring
  simpa only [pow_mul] using pow_le_pow_left₀ hV hsum C

/-- One exponent works for every later slack up to `N`; it depends only on the
fixed input, mesh and horizon exponents. -/
theorem uniform_atlas_power_budget (m J C : ℕ) (L f : ℝ) :
    ∃ M : ℕ, ∀ N K : ℝ, 2 ≤ N → 1 ≤ K → K ≤ N ^ m →
    ∀ D T : ℕ, (D : ℝ) ≤ N ^ (J + 1) → (2 : ℝ) ^ T ≤ 8 * N ^ L →
    ∀ q κ : ℝ, N ^ (-L) / 8 ≤ q → 0 < κ → κ ≤ N →
    (1 + N ^ m + K + (D : ℝ) + (2 : ℝ) ^ T +
      (4 * N ^ (-f) * ((2 * K + 2) * q) ^ 2 / κ)⁻¹) ^ C ≤ N ^ M := by
  obtain ⟨p, hp⟩ := exists_nat_ge
    (max (m : ℝ) (max ((J + 1 : ℕ) : ℝ) (max (L + 3) (5 + f + 2 * L))))
  have hmp : m ≤ p := by exact_mod_cast (le_max_left _ _).trans hp
  have hJp : J + 1 ≤ p := by
    exact_mod_cast ((le_max_left _ _).trans (le_max_right _ _)).trans hp
  have hLp : L + 3 ≤ (p : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hp)
  have hfp : 5 + f + 2 * L ≤ (p : ℝ) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hp)
  refine ⟨(p + 3) * C, ?_⟩
  intro N K hN hK hKH D T hD hT q κ hq hκ hκN
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hH : N ^ m ≤ N ^ p := pow_le_pow_right₀ hN₁ hmp
  have hDp : (D : ℝ) ≤ N ^ p := hD.trans (pow_le_pow_right₀ hN₁ hJp)
  have hTsmall : (8 : ℝ) ≤ N ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
    norm_num at hh
    exact hh
  have hT' : (2 : ℝ) ^ T ≤ N ^ p := by
    calc
      _ ≤ 8 * N ^ L := hT
      _ ≤ N ^ 3 * N ^ L := mul_le_mul_of_nonneg_right hTsmall (by positivity)
      _ = N ^ (L + 3) := by rw [Real.rpow_add hN₀]; norm_num; ring
      _ ≤ N ^ (p : ℝ) := Real.rpow_le_rpow_of_exponent_le hN₁ hLp
      _ = N ^ p := Real.rpow_natCast _ _
  have hfour : (16 : ℝ) ≤ N ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 4
    norm_num at hh
    exact hh
  have hτ : (4 * N ^ (-f) * ((2 * K + 2) * q) ^ 2 / κ)⁻¹ ≤ N ^ p := by
    calc
      _ ≤ 16 * N ^ (1 + f + 2 * L) := atlas_threshold_inverse_bound hN₁ hK hq hκ hκN
      _ ≤ N ^ 4 * N ^ (1 + f + 2 * L) :=
        mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = N ^ (5 + f + 2 * L) := by
        rw [show 5 + f + 2 * L = (4 : ℝ) + (1 + f + 2 * L) by ring]
        simp only [Real.rpow_add hN₀]
        norm_num
      _ ≤ N ^ (p : ℝ) := Real.rpow_le_rpow_of_exponent_le hN₁ hfp
      _ = N ^ p := Real.rpow_natCast _ _
  exact atlas_six_term_budget hN hH (hKH.trans hH) hDp hT' hτ (by positivity)

end Submission.Obl.k4_horizon_chart_assembly
