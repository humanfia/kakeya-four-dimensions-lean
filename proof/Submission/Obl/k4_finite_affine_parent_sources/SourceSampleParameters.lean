import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleNumerics

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The original depth error and gain are smaller than each reserved budget. -/
theorem selection_grid_errors {n : ℕ} {ρ gain unit δ₀ L : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hg : 0 ≤ gain) (hL : 0 ≤ L)
    (hδ : δ₀ ≤ ρ * gain)
    (hgain : gain * (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) ≤ unit) :
    2 * δ₀ ≤ unit ∧ 100 * gain ≤ unit ∧ 2 * (δ₀ * L) ≤ selectionBudget n ρ unit L := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ groupsC := Nat.cast_nonneg _
  have hfac : (100 : ℝ) ≤ 10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2) := by
    calc (100 : ℝ) ≤ 10 ^ 12 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr <;> linarith
  have hg100 : 100 * gain ≤ unit := by
    calc 100 * gain = gain * 100 := mul_comm _ _
      _ ≤ gain * (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) := by gcongr
      _ ≤ unit := hgain
  have h2δ : 2 * δ₀ ≤ unit := by
    have hδg : δ₀ ≤ gain := hδ.trans (by nlinarith [hg, hρ1])
    linarith
  refine ⟨h2δ, hg100, ?_⟩
  have hb : selectionBudget n ρ unit L =
      unit * L * ρ / (100000000 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) := by
    unfold selectionBudget stagePower
    field_simp
    <;> ring
  rw [hb, le_div_iff₀ (by positivity)]
  calc 2 * (δ₀ * L) * (100000000 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2))
      ≤ 2 * ((ρ * gain) * L) * (100000000 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) := by
          gcongr
    _ = (gain * (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2))) * (ρ * L) *
        (1 / 5000) := by ring
    _ ≤ unit * (ρ * L) * (1 / 5000) := by gcongr
    _ ≤ unit * L * ρ := by
        have hu : 0 ≤ unit := le_trans (by positivity) hg100
        nlinarith [mul_nonneg hu (mul_nonneg hρ.le hL)]

/-- The fixed sample budget pays all slack costs used for groups and local floors. -/
theorem sample_slack_costs {m : ℕ} {κ K A : ℝ} (hκ : 1 ≤ κ) (hK : 1 ≤ K)
    (hstrong : 10 ^ 40 * κ ^ 20 * K ^ 4 * ((m : ℝ) + 2) ^ 4 ≤ A) :
    10000 ≤ A ∧ 7 * κ ≤ A ∧ 192 * (7 * κ) ^ 3 ≤ A ∧
      1024 * (m : ℝ) * κ ^ 2 ≤ A ∧ 10 ^ 6 * ((m : ℝ) + 1) ^ 2 * κ ^ 12 ≤ A := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hKp : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hm1 : 1 ≤ ((m : ℝ) + 2) ^ 4 := one_le_pow₀ (by linarith)
  have hκ1 : 1 ≤ κ ^ 20 := one_le_pow₀ hκ
  have hκself : κ ≤ κ ^ 20 := le_self_pow₀ hκ (by norm_num)
  have hA : 10000 ≤ A := by
    apply le_trans _ hstrong
    calc (10000 : ℝ) = 10000 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have h7 : 7 * κ ≤ A := by
    apply le_trans _ hstrong
    calc 7 * κ = 7 * κ * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have h192 : 192 * (7 * κ) ^ 3 ≤ A := by
    apply le_trans _ hstrong
    calc 192 * (7 * κ) ^ 3 = 65856 * κ ^ 3 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have h1024 : 1024 * (m : ℝ) * κ ^ 2 ≤ A := by
    apply le_trans _ hstrong
    have hm : (m : ℝ) ≤ ((m : ℝ) + 2) ^ 4 := by
      calc (m : ℝ) ≤ (m : ℝ) + 2 := by linarith
        _ ≤ _ := le_self_pow₀ (by linarith) (by norm_num)
    calc 1024 * (m : ℝ) * κ ^ 2 = 1024 * κ ^ 2 * 1 * (m : ℝ) := by ring
      _ ≤ _ := by gcongr <;> norm_num
  refine ⟨hA, h7, h192, h1024, ?_⟩
  apply le_trans _ hstrong
  have hm : ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 2) ^ 4 := by
    calc ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 2) ^ 2 := by gcongr; linarith
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc 10 ^ 6 * ((m : ℝ) + 1) ^ 2 * κ ^ 12 = 10 ^ 6 * κ ^ 12 * 1 * ((m : ℝ) + 1) ^ 2 := by ring
    _ ≤ _ := by gcongr <;> norm_num

/-- The same lower bound pays the original share mask and the row coefficients. -/
theorem sample_share_row_cost {m : ℕ} {κ K A : ℝ} (hκ : 1 ≤ κ) (hK : 1 ≤ K)
    (hstrong : 10 ^ 40 * κ ^ 20 * K ^ 4 * ((m : ℝ) + 2) ^ 4 ≤ A) :
    16 * (m : ℝ) * κ ^ 3 ≤ A ∧ 12 * κ ≤ A := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hKp : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hm1 : 1 ≤ ((m : ℝ) + 2) ^ 4 := one_le_pow₀ (by linarith)
  have hmm : (m : ℝ) ≤ ((m : ℝ) + 2) ^ 4 := by
    calc (m : ℝ) ≤ (m : ℝ) + 2 := by linarith
      _ ≤ _ := le_self_pow₀ (by linarith) (by norm_num)
  have hκself : κ ≤ κ ^ 20 := le_self_pow₀ hκ (by norm_num)
  constructor
  · apply le_trans _ hstrong
    calc 16 * (m : ℝ) * κ ^ 3 = 16 * κ ^ 3 * 1 * (m : ℝ) := by ring
      _ ≤ _ := by gcongr <;> norm_num
  · apply le_trans _ hstrong
    calc 12 * κ = 12 * κ * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num

end

end Submission.Obl.k4_finite_affine_parent_sources
