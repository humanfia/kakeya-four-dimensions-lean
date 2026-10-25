import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

open Filter

namespace Submission.Obl.k4_two_velocity_row_list_completion

/-- A common polynomial budget for the double-counting and interpolation losses. -/
theorem row_count_polynomial {K R : ℝ} (hK : 1 ≤ K) (hR : 2 ≤ R)
    (hKR : K + 2 ≤ R) :
    2 * K ^ 2 * (K ^ 2 * (12 * R ^ 2 * (3 * K + 3) + 2) ^ 2) ≤
      16384 * R ^ 10 := by
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hKR' : K ≤ R := by linarith
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hD : 12 * R ^ 2 * (3 * K + 3) + 2 ≤ 74 * R ^ 3 := by
    calc
      _ ≤ 12 * R ^ 2 * (6 * R) + 2 := by gcongr; linarith
      _ = 72 * R ^ 3 + 2 := by ring
      _ ≤ 74 * R ^ 3 := by linarith
  have hpow : K ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ hK0 hKR' 4
  have hsq : (12 * R ^ 2 * (3 * K + 3) + 2) ^ 2 ≤ (74 * R ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hD 2
  calc
    _ = 2 * K ^ 4 * (12 * R ^ 2 * (3 * K + 3) + 2) ^ 2 := by ring
    _ ≤ 2 * R ^ 4 * (74 * R ^ 3) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hsq
        (sq_nonneg _) (by positivity)
    _ = 10952 * R ^ 10 := by ring
    _ ≤ 16384 * R ^ 10 :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hR0 _)

/-- Uniform choices of the input loss and interpolation scale, before any incidence data. -/
theorem choose_scales (S a ε : ℝ) (hS : 0 < S) (ha : 0 < a) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ R : ℝ, 2 ≤ R ∧ N ^ η + 2 ≤ R ∧ N ^ (-a) ≤ 1 / R ∧ 2 / R ≤ 1 ∧
        N ^ η * (2 / R) ^ S ≤ (1 / N ^ η) / 2 ∧ 16384 * R ^ 10 ≤ N ^ ε := by
  let b : ℝ := min (a / 2) (ε / 40)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  let η : ℝ := min (min (b / 4) (S * b / 8)) (ε / 2)
  have hη : 0 < η := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hηb : η ≤ b / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hηSb : η ≤ S * b / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hηε : η ≤ ε := by
    have h : η ≤ ε / 2 := min_le_right _ _
    linarith
  have hgap₁ : η < b := by linarith
  have hgap₂ : 2 * η < b * S := by nlinarith
  have hgap₃ : 10 * b < ε := by
    have h : b ≤ ε / 40 := min_le_right _ _
    linarith
  have hba : b ≤ a := by
    have h : b ≤ a / 2 := min_le_left _ _
    linarith
  have hlarge₁ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      (3 : ℝ) hgap₁
  have hlarge₂ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      (2 * (2 : ℝ) ^ S) hgap₂
  have hlarge₃ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      (16384 : ℝ) hgap₃
  have hscales : ∀ᶠ N : ℝ in atTop,
      ∃ R : ℝ, 2 ≤ R ∧ N ^ η + 2 ≤ R ∧ N ^ (-a) ≤ 1 / R ∧ 2 / R ≤ 1 ∧
        N ^ η * (2 / R) ^ S ≤ (1 / N ^ η) / 2 ∧ 16384 * R ^ 10 ≤ N ^ ε := by
    filter_upwards [hlarge₁, hlarge₂, hlarge₃, eventually_ge_atTop (2 : ℝ)]
      with N h₁ h₂ h₃ hN
    have hNpos : 0 < N := by linarith
    have hN1 : 1 ≤ N := by linarith
    let K : ℝ := N ^ η
    let R : ℝ := N ^ b
    have hK : 1 ≤ K := Real.one_le_rpow hN1 hη.le
    have hKpos : 0 < K := by positivity
    have hRpos : 0 < R := by positivity
    have hKR : K + 2 ≤ R := by change 3 * K ≤ R at h₁; linarith
    have hR : 2 ≤ R := by linarith
    have hmesh : N ^ (-a) ≤ 1 / R := by
      calc
        N ^ (-a) ≤ N ^ (-b) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg hba)
        _ = 1 / R := by rw [Real.rpow_neg hNpos.le]; simp only [R, one_div]
    have hcap : 2 * (2 : ℝ) ^ S * K ^ 2 ≤ R ^ S := by
      dsimp only [K, R]
      rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_mul hNpos.le]
      simpa only [Nat.cast_ofNat, mul_comm η (2 : ℝ)] using h₂
    have hnear : K * (2 / R) ^ S ≤ (1 / K) / 2 := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hRpos.le, div_div]
      apply (le_div_iff₀ (mul_pos hKpos (by norm_num : (0 : ℝ) < 2))).mpr
      have heq : K * ((2 : ℝ) ^ S / R ^ S) * (K * 2) =
          (2 * (2 : ℝ) ^ S * K ^ 2) / R ^ S := by ring
      rw [heq]
      exact (div_le_one (Real.rpow_pos_of_pos hRpos S)).mpr hcap
    have hbudget : 16384 * R ^ 10 ≤ N ^ ε := by
      dsimp only [R]
      rw [← Real.rpow_mul_natCast hNpos.le]
      simpa only [Nat.cast_ofNat, mul_comm b (10 : ℝ)] using h₃
    exact ⟨R, hR, hKR, hmesh, (div_le_one hRpos).mpr hR, hnear, hbudget⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hscales
  refine ⟨η, hη, hηε, max 2 M, le_max_left _ _, ?_⟩
  intro N hN
  exact hM N ((le_max_right _ _).trans hN)

end Submission.Obl.k4_two_velocity_row_list_completion
