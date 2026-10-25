-- Adapted from this LOT tree, o117, session x0390, commit 0d48789,
-- Submission/Obl/k4_quadratic_candidate_atlas_conversion/CoverageNumerics.lean.

import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_quadratic_finite_greedy_cover

open Filter

/-- A polynomial family and its priority Boolean formulas have one fixed
complexity exponent, chosen independently of the eventual small slack. -/
theorem priority_polynomial_complexity
    (N a ε C n : ℝ) (Mp Mg : ℕ) (hNlarge : 194 ≤ N) (ha : 0 ≤ a)
    (hε : ε ≤ 1) (hC : C ≤ N ^ Mp) (hn : n ≤ C * N ^ (a + ε))
    (hMg : 2 * (Mp : ℝ) + a + 3 ≤ (Mg : ℝ)) :
    n ≤ N ^ Mg ∧ (n + 1) * (N ^ Mp + 96) ≤ N ^ Mg := by
  have hN : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hpow : (0 : ℝ) ≤ N ^ (a + ε) := Real.rpow_nonneg hNpos.le _
  have hn' : n ≤ N ^ ((Mp : ℝ) + a + 1) := by
    calc
      _ ≤ N ^ Mp * N ^ (a + ε) := hn.trans (mul_le_mul_of_nonneg_right hC hpow)
      _ = N ^ ((Mp : ℝ) + a + ε) := by
        rw [← Real.rpow_natCast N Mp, ← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have he : 0 ≤ (Mp : ℝ) + a + 1 := by positivity
  have hunit : 1 ≤ N ^ ((Mp : ℝ) + a + 1) := Real.one_le_rpow hN he
  have hMp : 1 ≤ N ^ Mp := one_le_pow₀ hN
  have hplus : n + 1 ≤ 2 * N ^ ((Mp : ℝ) + a + 1) := by linarith
  have hformat : N ^ Mp + 96 ≤ 97 * N ^ Mp := by linarith
  have hnum : (n + 1) * (N ^ Mp + 96) ≤ N ^ Mg := by
    calc
      _ ≤ (2 * N ^ ((Mp : ℝ) + a + 1)) * (97 * N ^ Mp) :=
        mul_le_mul hplus hformat (by positivity) (by positivity)
      _ = 194 * (N ^ ((Mp : ℝ) + a + 1) * N ^ Mp) := by ring
      _ ≤ N * (N ^ ((Mp : ℝ) + a + 1) * N ^ Mp) := by gcongr
      _ = N ^ (2 * (Mp : ℝ) + a + 2) := by
        calc
          _ = N * N ^ (((Mp : ℝ) + a + 1) + (Mp : ℝ)) := by
            rw [← Real.rpow_natCast N Mp, ← Real.rpow_add hNpos]
          _ = N ^ (1 + (((Mp : ℝ) + a + 1) + (Mp : ℝ))) := by
            conv_rhs => rw [Real.rpow_add hNpos, Real.rpow_one]
          _ = _ := by congr 1; ring
      _ ≤ N ^ Mg := by
        rw [← Real.rpow_natCast N Mg]
        exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  refine ⟨hn'.trans ?_, hnum⟩
  rw [← Real.rpow_natCast N Mg]
  apply Real.rpow_le_rpow_of_exponent_le hN
  have : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
  linarith

/-- A fixed menu cost and the inverse-cubic derivative loss are absorbed by
the final inverse power when the path slack exponent is chosen small first. -/
theorem eventual_coverage_budget
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (a ε D : ℝ) (ha : 0 < a) (hε : 0 < ε) (hD : 0 < D) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ κ εin : ℝ,
      0 < κ → κ ≤ N k ^ σ → 0 ≤ εin →
      2 ≤ N k ^ (a + εin) ∧ 2 ≤ N k ^ ε ∧
      N k ^ (-ε) ≤ (κ⁻¹ / 2) / D - 8 / (N k ^ (a + εin)) ^ 3 := by
  let σ := min (ε / 4) (a / 4)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hσε : σ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hσa : σ < 3 * a := (min_le_right _ _).trans_lt (by linarith)
  have hm := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (a := -ε) (b := -σ) (by linarith) (4 * D)
  have hl := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (a := -(3 * a)) (b := -σ) (by linarith) (32 * D)
  have hk := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (a := 0) (b := a) ha 2
  have he := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (a := 0) (b := ε) hε 2
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hm, hl, hk, he] with k hm hl hk he
  intro κ εin hκ hκup hεin
  have hNkpos : 0 < N k := lt_of_lt_of_le zero_lt_one (hN k)
  have hKbase : N k ^ a ≤ N k ^ (a + εin) :=
    Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith)
  have hKpos : 0 < N k ^ (a + εin) := Real.rpow_pos_of_pos hNkpos _
  have hinv : N k ^ (-σ) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hNkpos.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hNkpos _) hκ).mpr hκup
  have hmass : N k ^ (-ε) ≤ N k ^ (-σ) / (4 * D) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hKinv : 8 / (N k ^ (a + εin)) ^ 3 ≤ 8 * N k ^ (-(3 * a)) := by
    have hKcube : (N k ^ a) ^ 3 ≤ (N k ^ (a + εin)) ^ 3 := by gcongr
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
      (by positivity : 0 < (N k ^ a) ^ 3) hKcube
    convert hh using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNkpos.le, div_eq_mul_inv,
      ← Real.rpow_neg hNkpos.le]
    congr 2
    ring
  have hloss : 8 / (N k ^ (a + εin)) ^ 3 ≤ N k ^ (-σ) / (4 * D) := by
    apply hKinv.trans
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨(by simpa only [Real.rpow_zero, mul_one] using hk.le.trans hKbase),
    (by simpa only [Real.rpow_zero, mul_one] using he.le), ?_⟩
  have hmain : N k ^ (-σ) / (2 * D) ≤ (κ⁻¹ / 2) / D := by
    calc
      _ ≤ κ⁻¹ / (2 * D) := div_le_div_of_nonneg_right hinv (by positivity)
      _ = _ := by ring
  have heq : N k ^ (-σ) / (2 * D) =
      N k ^ (-σ) / (4 * D) + N k ^ (-σ) / (4 * D) := by ring
  rw [heq] at hmain
  linarith

end Submission.Obl.k4_quadratic_finite_greedy_cover
