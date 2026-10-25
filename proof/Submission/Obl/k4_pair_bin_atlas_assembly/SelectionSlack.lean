import Mathlib

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Filter

/-- One small input slack simultaneously leaves room for the fixed list
factor and makes the relative anchor error at most one quarter. -/
theorem exists_selection_slack (a ε K : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ η ≤ 1 ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N κ : ℝ, N₀ ≤ N → 1 ≤ κ → κ ≤ N ^ η →
        2 ≤ N ^ a ∧ κ * (N ^ a)⁻¹ ≤ 1 / 4 ∧ K * κ ≤ N ^ ε := by
  let η : ℝ := min 1 (min (a / 2) (ε / 2))
  have hη : 0 < η := lt_min zero_lt_one (lt_min (by linarith) (by linarith))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηa : η ≤ a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have ha2 : 0 < a / 2 := by linarith
  have hε2 : 0 < ε / 2 := by linarith
  have hlarga : ∀ᶠ N : ℝ in atTop, 4 ≤ N ^ (a / 2) :=
    (tendsto_rpow_atTop ha2).eventually (eventually_ge_atTop 4)
  have hlargε : ∀ᶠ N : ℝ in atTop, K ≤ N ^ (ε / 2) :=
    (tendsto_rpow_atTop hε2).eventually (eventually_ge_atTop K)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlarga.and hlargε)
  refine ⟨η, hη, by linarith, hη1, max 2 N₀, le_max_left _ _, ?_⟩
  intro N κ hN hκ hκη
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  obtain ⟨hNa2, hNε2⟩ := hN₀ N ((le_max_right _ _).trans hN)
  have hκa : κ ≤ N ^ (a / 2) := hκη.trans (Real.rpow_le_rpow_of_exponent_le hN1 hηa)
  have hκε : κ ≤ N ^ (ε / 2) := hκη.trans (Real.rpow_le_rpow_of_exponent_le hN1 hηε)
  have hsqa : (N ^ (a / 2)) ^ 2 = N ^ a := by
    rw [pow_two, ← Real.rpow_add hN0]
    congr 1
    ring
  have hNa : 2 ≤ N ^ a := by rw [← hsqa]; nlinarith
  refine ⟨hNa, ?_, ?_⟩
  · rw [← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hN0 _), ← hsqa]
    nlinarith
  · calc
      K * κ ≤ N ^ (ε / 2) * N ^ (ε / 2) :=
        mul_le_mul hNε2 hκε (by linarith) (by positivity)
      _ = N ^ ε := by rw [← Real.rpow_add hN0]; congr 1; ring

/-- The two short-interval interpolation requirements hold uniformly at
all sufficiently large resolutions. -/
theorem exists_interpolation_scale {a CR CK C₂ : ℝ} (ha : 0 < a)
    (hCR : 0 < CR) (hfit : CK + 2 * CR < C₂) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      N ^ (-(CR * a)) ≤ 1 / 2 ∧
        256 * N ^ ((CK + 2 * CR) * a) ≤ N ^ (C₂ * a) := by
  have hp : 0 < CR * a := mul_pos hCR ha
  have hg : 0 < (C₂ - (CK + 2 * CR)) * a := mul_pos (sub_pos.mpr hfit) ha
  have hl : ∀ᶠ N : ℝ in atTop, 2 ≤ N ^ (CR * a) :=
    (tendsto_rpow_atTop hp).eventually (eventually_ge_atTop 2)
  have hr : ∀ᶠ N : ℝ in atTop, 256 ≤ N ^ ((C₂ - (CK + 2 * CR)) * a) :=
    (tendsto_rpow_atTop hg).eventually (eventually_ge_atTop 256)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hl.and hr)
  refine ⟨max 2 N₀, le_max_left _ _, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
    ((le_max_left _ _).trans hN)
  obtain ⟨hleft, hright⟩ := hN₀ N ((le_max_right _ _).trans hN)
  constructor
  · rw [Real.rpow_neg hN0.le]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hleft
  · calc
      _ ≤ N ^ ((C₂ - (CK + 2 * CR)) * a) * N ^ ((CK + 2 * CR) * a) :=
        mul_le_mul_of_nonneg_right hright (by positivity)
      _ = N ^ (C₂ * a) := by rw [← Real.rpow_add hN0]; congr 1; ring

end Submission.Obl.k4_pair_bin_atlas_assembly
