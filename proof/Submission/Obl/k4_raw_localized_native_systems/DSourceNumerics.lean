import Submission.Obl.k4_raw_localized_native_systems.Window.EventuallyRawBounds

namespace Submission.Obl.k4_raw_localized_native_systems

open Filter

/-- The source recipe keeps the earlier depth strictly below the frozen
scalar depth and gives every quantitative input of the D-side data theorem. -/
theorem source_recipe_bounds {s χ ν ε band kr r₀ : ℝ}
    (hχ : 0 < χ) (hs : s ≤ 1) (hν : 0 < ν)
    (hνs : ν ≤ s / 8) (hνχ : ν ≤ χ / 100)
    (hε : ε ≤ ν / 2) (hband : band ≤ ν / 10) (hkr : kr ≤ 1)
    (hr : |r₀ - (s - 2 * ν)| ≤ ε) (hr' : r₀ ≤ s - 2 * ν) :
    r₀ + ν ≤ s ∧ s - r₀ + 2 * ν ≤ 2 * χ ∧
      band ≤ χ / 1000 ∧ band ≤ 1 / 80 ∧ kr * (s - 2 * ν) + ε ≤ 1 := by
  have hrlo := (abs_le.mp hr).1
  have hsd : 0 ≤ s - 2 * ν := by linarith only [hνs, hν]
  have htime : kr * (s - 2 * ν) ≤ s - 2 * ν := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hkr hsd
  exact ⟨by linarith only [hr', hν], by linarith only [hrlo, hε, hνχ, hχ],
    by linarith only [hband, hνχ], by linarith only [hband, hνs, hs],
    by linarith only [htime, hε, hs, hν]⟩

/-- Ceilings of real source list bounds still have subpower size. -/
theorem eventually_source_list_ceil {N κ : ℕ → ℝ}
    (hN : ∀ n, 1 ≤ N n) (hNt : Tendsto N atTop atTop) (hκ : ∀ n, 1 ≤ κ n)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, κ n ≤ N n ^ ε)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ n in atTop, (⌈κ n⌉₊ : ℝ) ≤ N n ^ σ := by
  have hh := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 1 hσ (by norm_num : (0 : ℝ) ≤ 2)
  filter_upwards [hh] with n hn
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ κ n by linarith [hκ n])).le
  have h2 : 2 * κ n ≤ N n ^ σ := by
    simpa only [pow_one, Real.rpow_zero, mul_one] using hn.le
  linarith only [hc, h2, hκ n]

/-- A fixed small power pays the ceiling of every admissible current list
bound, uniformly in the loss variable. -/
theorem current_list_ceil_le {N loss σ : ℝ} (hN : 1 ≤ N) (hloss : 0 ≤ loss)
    (hσ : 2 ≤ N ^ σ) : (⌈N ^ loss⌉₊ : ℝ) ≤ N ^ (loss + σ) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpower := Real.one_le_rpow hN hloss
  have hc := (Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le loss)).le
  calc
    _ ≤ 2 * N ^ loss := by linarith only [hc, hpower]
    _ ≤ N ^ loss * N ^ σ := by nlinarith only [hσ, hpower]
    _ = _ := (Real.rpow_add hN0 _ _).symm

/-- All polynomial and scalar allowances for the finite raw constructor.
The original source slack is `κ`; the full masked floor uses `2κ`. -/
structure RawSampleBounds (N κ K χ τ r s band u : ℝ) : Prop where
  largeScale : 256 ≤ N
  chiPower : 2 ≤ N ^ χ
  sourceCover : 2 * κ ≤ K
  packingPositive : 1 ≤ K
  packingQuadratic : 2 * (2 * κ) ^ 2 ≤ K
  packingScale : K ≤ N
  densityBudget : 64 * (2 * κ) ^ 3 * N ^ τ ≤ N ^ χ
  scalarBudget : 1 + 2 * κ ≤ N ^ χ
  valueBudget : 2 * κ * k4_finite_width_output_exclusion.δ N r ≤ N ^ χ * N ^ (-s + χ)
  curvatureBudget : 2 * κ / k4_finite_width_output_exclusion.δ N r ≤ N ^ χ / N ^ (-s + χ)
  angleBudget : 32 * (2 * κ) * N ^ u ≤ N
  errorBudget : N ^ (2 * band + u) ≤ N ^ (4 : ℕ)
  polynomialBudget : 2097152 * Real.pi * K ^ (8 + 1) ≤ N ^ (χ / 2)

/-- A single positive allowance for current slack pays every raw polynomial
on the same original source subsequence. It is fixed before the loss variable. -/
theorem exists_raw_sample_bounds {N κ : ℕ → ℝ}
    (hN : ∀ n, 1 ≤ N n) (hNt : Tendsto N atTop atTop) (hκ : ∀ n, 1 ≤ κ n)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, κ n ≤ N n ^ ε)
    {χ τ u ε r s band : ℝ} (hχ : 0 < χ) (hτ : τ < χ) (hu : u < 1)
    (hε : 0 < ε) (hgap : r + ε ≤ s) (hclose : s - r + 2 * ε ≤ 2 * χ)
    (hband : 2 * band + u ≤ 4) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ᶠ n in atTop,
      RawSampleBounds (N n) (κ n) (N n ^ e) χ τ r s band u ∧
      ∀ loss : ℝ, loss ≤ e → N n ^ loss ≤ N n ^ e := by
  let e := min (χ / 1000) (1 / 1000 : ℝ)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have heχ : e ≤ χ / 1000 := min_le_left _ _
  have he1 : e ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have h2κ : ∀ n, 1 ≤ 2 * κ n := fun n => by linarith [hκ n]
  have h2sub (a : ℝ) (ha : 0 < a) : ∀ᶠ n in atTop, 2 * κ n ≤ N n ^ a := by
    have hh := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN hNt hκ hsub 1 ha (by norm_num : (0 : ℝ) ≤ 2)
    filter_upwards [hh] with n hn
    simpa only [pow_one, Real.rpow_zero, mul_one] using hn.le
  have hraw := Window.eventually_raw_bounds hN hNt h2κ h2sub hχ hτ hu hε hgap hclose
  have hquad := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 2 he (by norm_num : (0 : ℝ) ≤ 8)
  have hpoly := k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (show e * 9 < χ / 2 by linarith only [heχ, hχ]) (2097152 * Real.pi)
  refine ⟨e, he, he1, ?_⟩
  filter_upwards [hraw, hquad, hpoly] with n hn hq hp
  obtain ⟨hlarge, hchi, hdensity, hscalar, -, hangle, hvalue, hcurv⟩ := hn
  have hN0 : 0 < N n := lt_of_lt_of_le zero_lt_one (hN n)
  have hquadratic : 2 * (2 * κ n) ^ 2 ≤ N n ^ e := by
    have hh : 8 * κ n ^ 2 ≤ N n ^ e := by
      simpa only [Real.rpow_zero, mul_one] using hq.le
    nlinarith only [hh]
  have hcover : 2 * κ n ≤ N n ^ e := by
    apply le_trans _ hquadratic
    nlinarith only [hκ n]
  refine ⟨⟨hlarge, hchi, hcover,
    Real.one_le_rpow (hN n) he.le, hquadratic,
    ?_, hdensity, hscalar, hvalue, hcurv, hangle, ?_, ?_⟩,
    fun loss hloss => Real.rpow_le_rpow_of_exponent_le (hN n) hloss⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (hN n) he1
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (hN n) hband
  · have hpower : (N n ^ e) ^ (8 + 1 : ℕ) = N n ^ (e * 9) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      norm_num
    rw [hpower]
    exact hp.le

end Submission.Obl.k4_raw_localized_native_systems
