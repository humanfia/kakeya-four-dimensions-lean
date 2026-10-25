import Submission.Lib.K4ModelReduction.Diagonal

/-! Finite exponent grids for simultaneous deletion-based preparation. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open Filter

def positiveScaleGrid (M L : ℕ) : Finset ℝ :=
  (Finset.Icc 1 (L * M)).image (fun j : ℕ => (j : ℝ) / M)

theorem positiveScaleGrid_card_le (M L : ℕ) : (positiveScaleGrid M L).card ≤ L * M := by
  classical
  unfold positiveScaleGrid
  exact Finset.card_image_le.trans (by simp [Nat.card_Icc])

/-- Rounding upward stays in the finite exponent grid and costs less than one
grid step. Lower floors are asserted at these grid points, not at all real scales. -/
theorem exists_positiveScaleGrid_point (M L : ℕ) (hM : 0 < M) {r : ℝ}
    (hr : 0 < r) (hrL : r ≤ L) :
    ∃ s ∈ positiveScaleGrid M L, r ≤ s ∧ s < r + 1 / M := by
  classical
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  let j : ℕ := ⌈r * (M : ℝ)⌉₊
  have hj0 : 0 < j := Nat.ceil_pos.mpr (mul_pos hr hMreal)
  have hjL : j ≤ L * M := Nat.ceil_le.mpr (by
    exact_mod_cast mul_le_mul_of_nonneg_right hrL hMreal.le)
  refine ⟨(j : ℝ) / M, Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj0, hjL⟩, rfl⟩, ?_, ?_⟩
  · exact (le_div_iff₀ hMreal).mpr (Nat.le_ceil _)
  · apply (div_lt_iff₀ hMreal).mpr
    have hj := Nat.ceil_lt_add_one (mul_nonneg hr.le hMreal.le)
    calc
      (j : ℝ) < r * M + 1 := hj
      _ = (r + 1 / M) * M := by field_simp

/-- Exponent-rounding losses are subpower as soon as the resolution tends to
infinity, independently of the speed at which the base resolution grows. -/
theorem eventually_scale_rounding_loss_le (N : ℕ → ℝ) (M : ℕ → ℕ)
    (hN : ∀ k, 1 ≤ N k) (hM : Tendsto M atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, N k ^ (1 / (M k : ℝ)) ≤ N k ^ ε := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ε⁻¹
  filter_upwards [hM.eventually_ge_atTop J] with k hk
  have hMJ : ε⁻¹ ≤ (M k : ℝ) := hJ.le.trans (by exact_mod_cast hk)
  have hexp : 1 / (M k : ℝ) ≤ ε := by
    have h := one_div_le_one_div_of_le (inv_pos.mpr hε) hMJ
    simpa only [one_div, inv_inv] using h
  exact Real.rpow_le_rpow_of_exponent_le (hN k) hexp

/-- There is a single monotonically growing grid resolution for which both
the number of tested scales and their exponent-rounding loss are subpower. -/
theorem exists_subpower_scale_resolution (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) :
    ∃ M : ℕ → ℕ, Monotone M ∧ (∀ k, 1 ≤ M k) ∧ Tendsto M atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        (M k : ℝ) ≤ N k ^ ε ∧ N k ^ (1 / (M k : ℝ)) ≤ N k ^ ε := by
  let P : ℕ → ℕ → Prop := fun j k =>
    (j : ℝ) + 1 ≤ N k ^ (1 / ((j : ℝ) + 1))
  have hP (j : ℕ) : ∀ᶠ k in atTop, P j k :=
    ((tendsto_rpow_atTop (by positivity : 0 < 1 / ((j : ℝ) + 1))).comp hNt).eventually_ge_atTop _
  obtain ⟨m, hm, hmt, hmn, hdiag⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal P hP
  let M : ℕ → ℕ := fun k => m k + 1
  have hMmono : Monotone M := fun i j hij => Nat.add_le_add_right (hm hij) 1
  have hM1 (k : ℕ) : 1 ≤ M k := by dsimp [M]; omega
  have hMt : Tendsto M atTop atTop := (tendsto_add_atTop_nat 1).comp hmt
  have hbound : ∀ᶠ k in atTop, (M k : ℝ) ≤ N k ^ (1 / (M k : ℝ)) := by
    filter_upwards [hdiag] with k hk
    simpa only [P, M, Nat.cast_add, Nat.cast_one] using hk (m k) le_rfl
  refine ⟨M, hMmono, hM1, hMt, ?_⟩
  intro ε hε
  have hround := eventually_scale_rounding_loss_le N M (fun k => by linarith [hN k]) hMt hε
  filter_upwards [hbound, hround] with k hk hr
  exact ⟨hk.trans hr, hr⟩

/-- A single subpower buffer can be chosen before every fixed polynomial
loss. Applying this to the product of the old loss, grid size, and rounding
factor keeps the preparation certificate uniform over compact scale ranges. -/
theorem exists_subpower_polynomial_buffer (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε) :
    ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      ∀ (p : ℕ) (C : ℝ), ∀ᶠ k in atTop, C * (K k) ^ p ≤ H k := by
  let P : ℕ → ℕ → Prop := fun j k =>
    (K k * ((j + 1 : ℕ) : ℝ)) ^ (j + 1) ≤ N k ^ (1 / ((j + 1 : ℕ) : ℝ))
  have hP (j : ℕ) : ∀ᶠ k in atTop, P j k := by
    let m := j + 1
    let e : ℝ := 1 / (2 * (m : ℝ) ^ 2)
    have hm : 0 < m := by dsimp [m]; omega
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
    have he : 0 < e := by dsimp [e]; positivity
    have hconst : ∀ᶠ k in atTop, (m : ℝ) ^ m ≤ N k ^ (1 / (2 * (m : ℝ))) :=
      ((tendsto_rpow_atTop (by positivity : 0 < 1 / (2 * (m : ℝ)))).comp hNt).eventually_ge_atTop _
    filter_upwards [hsub e he, hconst] with k hk hc
    have hNpos : 0 < N k := by linarith [hN k]
    change (K k * (m : ℝ)) ^ m ≤ N k ^ (1 / (m : ℝ))
    calc
      (K k * (m : ℝ)) ^ m = (K k) ^ m * (m : ℝ) ^ m := mul_pow _ _ _
      _ ≤ (N k ^ e) ^ m * N k ^ (1 / (2 * (m : ℝ))) :=
        mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans (hK k)) hk m) hc
          (by positivity) (by positivity)
      _ = N k ^ (1 / (m : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
        congr 1
        dsimp [e]
        field_simp
        ring
  obtain ⟨m, hm, hmt, hmn, hdiag⟩ := Submission.Lib.K4ModelReduction.exists_slow_diagonal P hP
  let J : ℕ → ℕ := fun k => m k + 1
  let H : ℕ → ℝ := fun k => (K k * (J k : ℝ)) ^ (J k)
  have hJ1 (k : ℕ) : 1 ≤ J k := by dsimp [J]; omega
  have hJreal1 (k : ℕ) : (1 : ℝ) ≤ J k := by exact_mod_cast hJ1 k
  have hJt : Tendsto J atTop atTop := (tendsto_add_atTop_nat 1).comp hmt
  have hH1 (k : ℕ) : 1 ≤ H k := by
    apply one_le_pow₀
    calc
      1 ≤ K k := hK k
      _ = K k * 1 := by ring
      _ ≤ K k * (J k : ℝ) := mul_le_mul_of_nonneg_left (hJreal1 k) (zero_le_one.trans (hK k))
  have hbound : ∀ᶠ k in atTop, H k ≤ N k ^ (1 / (J k : ℝ)) := by
    filter_upwards [hdiag] with k hk
    simpa only [P, H, J, Nat.cast_add, Nat.cast_one] using hk (m k) le_rfl
  refine ⟨H, hH1, ?_, ?_⟩
  · intro ε hε
    have hround := eventually_scale_rounding_loss_le N J (fun k => by linarith [hN k]) hJt hε
    filter_upwards [hbound, hround] with k hk hr
    exact hk.trans hr
  · intro p C
    have hJreal : Tendsto (fun k => (J k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hJt
    filter_upwards [hJt.eventually_ge_atTop p, hJreal.eventually_ge_atTop C] with k hp hC
    have hJpow : (J k : ℝ) ≤ (J k : ℝ) ^ (J k) := by
      simpa only [pow_one] using pow_le_pow_right₀ (hJreal1 k) (hJ1 k)
    have hK0 : 0 ≤ K k := zero_le_one.trans (hK k)
    have hJ0 : (0 : ℝ) ≤ J k := zero_le_one.trans (hJreal1 k)
    calc
      C * (K k) ^ p ≤ (J k : ℝ) * (K k) ^ p :=
        mul_le_mul_of_nonneg_right hC (pow_nonneg hK0 _)
      _ ≤ (J k : ℝ) ^ (J k) * (K k) ^ (J k) :=
        mul_le_mul hJpow (pow_le_pow_right₀ (hK k) hp) (pow_nonneg hK0 _) (pow_nonneg hJ0 _)
      _ = H k := by dsimp [H]; rw [mul_pow]; ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
