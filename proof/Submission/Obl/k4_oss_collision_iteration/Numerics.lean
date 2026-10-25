import Submission.Obl.k4_oss_dyadic_reduction.Numerics

open Filter Set
open scoped ENNReal Topology

namespace Submission.Obl.k4_oss_collision_iteration

/-- Below the threshold there is bounded growth, and above it there is contraction. -/
theorem collision_iteration_bound (q : ℕ → ℝ≥0∞) (m : ℕ) (A B L : ℝ≥0∞)
    (hB : B ≤ 1) (hq : q 0 ≤ 1)
    (hgrowth : ∀ k < m, q (k + 1) ≤ L * q k)
    (hcontract : ∀ k < m, A ≤ q k → q (k + 1) ≤ B * q k) :
    q m ≤ max (L * A) (B ^ m) := by
  have hbound : ∀ k ≤ m, q k ≤ max (L * A) (B ^ k) := by
    intro k hk
    induction k with
    | zero => simpa using hq.trans (le_max_right (L * A) 1)
    | succ k ih =>
      have hkm : k < m := by omega
      have ih := ih (by omega)
      by_cases hA : A ≤ q k
      · calc
          q (k + 1) ≤ B * q k := hcontract k hkm hA
          _ ≤ B * max (L * A) (B ^ k) := by gcongr
          _ = max (B * (L * A)) (B ^ (k + 1)) := by rw [mul_max, pow_succ']
          _ ≤ max (L * A) (B ^ (k + 1)) := by
            exact max_le_max (mul_le_of_le_one_left' hB) le_rfl
      · calc
          q (k + 1) ≤ L * q k := hgrowth k hkm
          _ ≤ L * A := by gcongr; exact le_of_not_ge hA
          _ ≤ max (L * A) (B ^ (k + 1)) := le_max_left _ _
  exact hbound m le_rfl

/-- Choose a fixed number of contractions and absorb both fixed multiplicative constants. -/
theorem exists_iteration_parameters (L : ℝ) {c γ R : ℝ}
    (hc : 0 < c) (hγ : 0 < γ) (hR : 0 < R) :
    ∃ (m : ℕ) (r₀ : ℝ), 0 < r₀ ∧ r₀ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < r₀ → r < 1 ∧ 3 * r ^ c ≤ 1 ∧
        L * r ^ (1 - γ / 2) ≤ r ^ (1 - γ) ∧
        (3 * r ^ c) ^ m ≤ r ^ (1 - γ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / c)
  have hmc : 1 ≤ (c / 2) * (m : ℝ) := by
    have := (div_lt_iff₀ hc).mp hm
    nlinarith
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      r < min R 1 ∧ 3 * r ^ (c / 2) ≤ 1 ∧ L * r ^ (γ / 2) ≤ 1 := by
    filter_upwards [(show ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), r < min R 1 from
        Iio_mem_nhds (lt_min hR (by norm_num))).filter_mono nhdsWithin_le_nhds,
      Submission.Obl.k4_oss_dyadic_reduction.eventually_small_power 3 (by positivity : 0 < c / 2),
      Submission.Obl.k4_oss_dyadic_reduction.eventually_small_power L (by positivity : 0 < γ / 2)]
      with r hr h3 hL
    exact ⟨hr, h3, hL⟩
  obtain ⟨d, hd, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨m, min d R, lt_min hd hR, min_le_right _ _, ?_⟩
  intro r hr hrr
  obtain ⟨hrR1, h3, hL⟩ := hsmall ⟨hr, lt_of_lt_of_le hrr (min_le_left _ _)⟩
  have hr1 : r < 1 := (lt_min_iff.mp hrR1).2
  have hfactor : 3 * r ^ c ≤ r ^ (c / 2) := by
    calc
      3 * r ^ c = (3 * r ^ (c / 2)) * r ^ (c / 2) := by
        rw [mul_assoc, ← Real.rpow_add hr]
        congr 2
        ring
      _ ≤ 1 * r ^ (c / 2) := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hr.le _)
      _ = r ^ (c / 2) := one_mul _
  refine ⟨hr1, hfactor.trans (Real.rpow_le_one hr.le hr1.le (by positivity)), ?_, ?_⟩
  · calc
      L * r ^ (1 - γ / 2) = (L * r ^ (γ / 2)) * r ^ (1 - γ) := by
        rw [mul_assoc, ← Real.rpow_add hr]
        congr 2
        ring
      _ ≤ 1 * r ^ (1 - γ) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hr.le _)
      _ = r ^ (1 - γ) := one_mul _
  · calc
      (3 * r ^ c) ^ m ≤ (r ^ (c / 2)) ^ m := pow_le_pow_left₀ (by positivity) hfactor m
      _ = r ^ ((c / 2) * (m : ℝ)) := by rw [Real.rpow_mul hr.le, Real.rpow_natCast]
      _ ≤ r ^ (1 - γ) := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (by linarith)

/-- The finite iteration in the extended nonnegative reals, with all scale choices uniform. -/
theorem exists_collision_iteration (L : ℝ) {c γ R : ℝ}
    (hc : 0 < c) (hγ : 0 < γ) (hR : 0 < R) :
    ∃ (m : ℕ) (r₀ : ℝ), 0 < r₀ ∧ r₀ ≤ R ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ q : ℕ → ℝ≥0∞, q 0 ≤ 1 →
        (∀ k < m, q (k + 1) ≤ ENNReal.ofReal L * q k) →
        (∀ k < m, ENNReal.ofReal (r ^ (1 - γ / 2)) ≤ q k →
          q (k + 1) ≤ (3 * ENNReal.ofReal (r ^ c)) * q k) →
        q m ≤ ENNReal.ofReal (r ^ (1 - γ)) := by
  obtain ⟨m, r₀, hr₀, hr₀R, hnum⟩ := exists_iteration_parameters L hc hγ hR
  refine ⟨m, r₀, hr₀, hr₀R, ?_⟩
  intro r hr hrr q hq hgrowth hcontract
  obtain ⟨hr1, hfactor, hthreshold, hpower⟩ := hnum r hr hrr
  have hfactor' : 3 * ENNReal.ofReal (r ^ c) ≤ (1 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hfactor
  apply (collision_iteration_bound q m (ENNReal.ofReal (r ^ (1 - γ / 2)))
    (3 * ENNReal.ofReal (r ^ c)) (ENNReal.ofReal L) hfactor' hq hgrowth hcontract).trans
  apply max_le
  · calc
      ENNReal.ofReal L * ENNReal.ofReal (r ^ (1 - γ / 2)) =
          ENNReal.ofReal (L * r ^ (1 - γ / 2)) := by
        rw [mul_comm L, ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), mul_comm]
      _ ≤ ENNReal.ofReal (r ^ (1 - γ)) := ENNReal.ofReal_le_ofReal hthreshold
  · calc
      (3 * ENNReal.ofReal (r ^ c)) ^ m = ENNReal.ofReal ((3 * r ^ c) ^ m) := by
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ ENNReal.ofReal (r ^ (1 - γ)) := ENNReal.ofReal_le_ofReal hpower

end Submission.Obl.k4_oss_collision_iteration
