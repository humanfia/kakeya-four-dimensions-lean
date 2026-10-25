import Submission.Obl.k4_finite_affine_parent_sources.SourceEntropyBudget
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSample

/-! The sample's fixed lower bound, expressed in its native budget power. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The denominator of the fixed selection constant is at most one. -/
theorem selectionConst_lower {m n : ℕ} {T κ₁ ρ unit L : ℝ}
    (hT : 0 ≤ T) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : 0 < unit) (hu1 : unit ≤ 1) (hL : 0 < L) :
    (10 : ℝ) ^ 40 * ((m : ℝ) + 2) ^ 4 ≤ selectionConst m n T κ₁ ρ unit L := by
  have hmin : 0 < min L 1 := lt_min hL (by norm_num)
  have hden0 : 0 < κ₁ * ρ * unit * min L 1 := by positivity
  have hden1 : κ₁ * ρ * unit * min L 1 ≤ 1 := by
    calc κ₁ * ρ * unit * min L 1 ≤ 1 * 1 * 1 * 1 := by
          gcongr
          exact min_le_right _ _
      _ = 1 := by norm_num
  have hden : (κ₁ * ρ * unit * min L 1) ^ 8 ≤ 1 := by
    simpa using pow_le_pow_left₀ hden0.le hden1 8
  have hfac : 1 ≤ ((n : ℝ) + 2) * (T + 2) * ((groupsC : ℝ) + 2) := by
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ ((n : ℝ) + 2) * (T + 2) * ((groupsC : ℝ) + 2) := by
        gcongr <;> linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) groupsC]
  have hnum : 1 ≤ (((n : ℝ) + 2) * (T + 2) * ((groupsC : ℝ) + 2)) ^ 8 :=
    one_le_pow₀ hfac
  unfold selectionConst
  rw [le_div_iff₀ (by positivity)]
  calc (10 : ℝ) ^ 40 * ((m : ℝ) + 2) ^ 4 * (κ₁ * ρ * unit * min L 1) ^ 8
      ≤ (10 : ℝ) ^ 40 * ((m : ℝ) + 2) ^ 4 * 1 := by gcongr
    _ ≤ _ := by gcongr

/-- The very large fixed sample constant pays the logarithmic likelihood hypothesis. -/
theorem four_le_budget_log {Nk b : ℝ} (hNk : 0 < Nk) (hbig : 256 ≤ Nk ^ b) :
    4 ≤ b * Real.log Nk := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256) hbig
  rw [Real.log_rpow hNk] at h
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    have hpow : (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
    rw [hpow, Real.log_pow]
    norm_num
  rw [h256] at h
  nlinarith [Real.log_two_gt_d9]

/-- The budget is a power of the actual native scale. -/
theorem selection_budget_native (n : ℕ) (ρ unit L Nk : ℝ) (hNk : 0 ≤ Nk) :
    Nk ^ selectionBudget n ρ unit L =
      (Nk ^ (unit * L)) ^ (stagePower n ρ / (100 * ((groupsC : ℝ) + 2))) := by
  rw [← Real.rpow_mul hNk]
  unfold selectionBudget
  congr 1
  ring

/-- The sample lower bound also absorbs the old velocity radius and the path slack. -/
theorem sample_budget_lower {m n : ℕ} {T κ₁ ρ unit L Nk κ K : ℝ}
    (hT : 0 ≤ T) (hκ₁ : 0 < κ₁) (hκ₁1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : 0 < unit) (hu1 : unit ≤ 1) (hL : 0 < L) (hκ : 1 ≤ κ) (hK : 1 ≤ K)
    (hbig : κ ^ 20 * K ^ 4 * selectionConst m n T κ₁ ρ unit L ≤
      Nk ^ selectionBudget n ρ unit L) :
    (10 : ℝ) ^ 40 * κ ^ 20 * K ^ 4 * ((m : ℝ) + 2) ^ 4 ≤
      Nk ^ selectionBudget n ρ unit L := by
  have hc := selectionConst_lower (m := m) (n := n) hT hκ₁ hκ₁1 hρ hρ1 hu hu1 hL
  calc (10 : ℝ) ^ 40 * κ ^ 20 * K ^ 4 * ((m : ℝ) + 2) ^ 4
      = κ ^ 20 * K ^ 4 * ((10 : ℝ) ^ 40 * ((m : ℝ) + 2) ^ 4) := by ring
    _ ≤ κ ^ 20 * K ^ 4 * selectionConst m n T κ₁ ρ unit L := by gcongr
    _ ≤ _ := hbig

/-- The budget exponent is positive and costs at most one native power. -/
theorem selection_native_exponent {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 < stagePower n ρ / (100 * ((groupsC : ℝ) + 2)) ∧
      stagePower n ρ / (100 * ((groupsC : ℝ) + 2)) ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ groupsC := Nat.cast_nonneg _
  constructor
  · unfold stagePower
    positivity
  · rw [div_le_iff₀ (by positivity)]
    have hθ : stagePower n ρ ≤ 1 := by
      unfold stagePower
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith

/-- At an admissible sample the native scale is large, and covers the original
velocity radius, while its budget logarithm pays the window likelihood. -/
theorem sample_native_bounds {m n : ℕ} {T κ₁ ρ unit L Nk κ K : ℝ}
    (hT : 0 ≤ T) (hκ₁ : 0 < κ₁) (hκ₁1 : κ₁ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : 0 < unit) (hu1 : unit ≤ 1) (hL : 0 < L) (hκ : 1 ≤ κ) (hK : 1 ≤ K)
    (hNk : 1 < Nk)
    (hbig : κ ^ 20 * K ^ 4 * selectionConst m n T κ₁ ρ unit L ≤
      Nk ^ selectionBudget n ρ unit L) :
    256 ≤ Nk ^ (unit * L) ∧ K ≤ Nk ^ (unit * L) ∧ 7 * κ ≤ Nk ^ (unit * L) ∧
      4 ≤ (stagePower n ρ / (100 * ((groupsC : ℝ) + 2))) * Real.log (Nk ^ (unit * L)) := by
  have hlower := sample_budget_lower hT hκ₁ hκ₁1 hρ hρ1 hu hu1 hL hκ hK hbig
  have hm : 1 ≤ ((m : ℝ) + 2) ^ 4 :=
    one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hκp : 1 ≤ κ ^ 20 := one_le_pow₀ hκ
  have hKp : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hlarge : (10 : ℝ) ^ 40 ≤ Nk ^ selectionBudget n ρ unit L := by
    apply le_trans _ hlower
    calc (10 : ℝ) ^ 40 = (10 : ℝ) ^ 40 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hlarge256 : 256 ≤ Nk ^ selectionBudget n ρ unit L :=
    (by norm_num : (256 : ℝ) ≤ (10 : ℝ) ^ 40).trans hlarge
  have hsmall : Nk ^ selectionBudget n ρ unit L ≤ Nk ^ (unit * L) := by
    rw [selection_budget_native n ρ unit L Nk (by linarith)]
    have hN : 1 ≤ Nk ^ (unit * L) := Real.one_le_rpow hNk.le (by positivity)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN (selection_native_exponent hρ hρ1).2
  have hKself : K ≤ K ^ 4 := le_self_pow₀ hK (by norm_num)
  have hκself : κ ≤ κ ^ 20 := le_self_pow₀ hκ (by norm_num)
  refine ⟨hlarge256.trans hsmall, ?_, ?_, ?_⟩
  · apply le_trans _ (hlower.trans hsmall)
    calc K ≤ K ^ 4 := hKself
      _ = 1 * 1 * K ^ 4 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  · apply le_trans _ (hlower.trans hsmall)
    calc 7 * κ ≤ 7 * κ ^ 20 := mul_le_mul_of_nonneg_left hκself (by norm_num)
      _ = 7 * κ ^ 20 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  · have hlog := four_le_budget_log (by linarith : 0 < Nk) hlarge256
    rw [Real.log_rpow (by linarith : 0 < Nk)]
    convert hlog using 1 <;> unfold selectionBudget <;> ring

/-- A hundred group-budget powers are exactly the prescribed stage constant. -/
theorem selection_stage_power (n : ℕ) (ρ unit L Nk : ℝ) (hNk : 0 < Nk) :
    (Nk ^ selectionBudget n ρ unit L) ^ (100 * (groupsC + 2)) =
      (Nk ^ (unit * L)) ^ stagePower n ρ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hNk.le, ← Real.rpow_mul hNk.le]
  congr 1
  unfold selectionBudget
  push_cast
  field_simp

/-- The raw-cap intermediate constant fits into the native scale. -/
theorem selection_intermediate_power {n : ℕ} {ρ unit L Nk : ℝ}
    (hNk : 1 ≤ Nk) (huL : 0 ≤ unit * L) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (Nk ^ selectionBudget n ρ unit L) ^ (10 * (groupsC + 2)) ≤ Nk ^ (unit * L) := by
  have hNk0 : 0 < Nk := zero_lt_one.trans_le hNk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ groupsC := Nat.cast_nonneg _
  have hθ : stagePower n ρ ≤ 1 := by
    unfold stagePower
    rw [div_le_iff₀ (by positivity)]
    linarith
  have heq : (Nk ^ selectionBudget n ρ unit L) ^ (10 * (groupsC + 2)) =
      Nk ^ (unit * L * (stagePower n ρ / 10)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNk0.le]
    congr 1
    unfold selectionBudget
    push_cast
    field_simp
    <;> ring
  rw [heq]
  apply Real.rpow_le_rpow_of_exponent_le hNk
  have hθ10 : stagePower n ρ / 10 ≤ 1 := by linarith
  simpa using mul_le_mul_of_nonneg_left hθ10 huL

/-- The entire intermediate group alphabet fits below the native scale. -/
theorem selection_group_power {n : ℕ} {ρ unit L Nk : ℝ}
    (hNk : 1 ≤ Nk) (huL : 0 ≤ unit * L) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (Nk ^ selectionBudget n ρ unit L) ^ (6 * groupsC) ≤ Nk ^ (unit * L) := by
  have hA : 1 ≤ Nk ^ selectionBudget n ρ unit L := by
    apply Real.one_le_rpow hNk
    unfold selectionBudget stagePower
    positivity
  exact (pow_le_pow_right₀ hA (by omega : 6 * groupsC ≤ 10 * (groupsC + 2))).trans
    (selection_intermediate_power hNk huL hρ hρ1)

end

end Submission.Obl.k4_finite_affine_parent_sources
