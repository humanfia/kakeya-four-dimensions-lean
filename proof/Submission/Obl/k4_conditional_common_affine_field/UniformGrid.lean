import Mathlib
import Submission.Obl.k4_conditional_common_affine_field.GridField
import Submission.Obl.k4_conditional_common_affine_field.UniformGridField

set_option autoImplicit false

/-!
# The grid field with one polynomial budget

`uniformGridField : UniformGridField` (the interface of session x0968's assembly), from the
explicit bounds of `grid_common_field`, with the exponent `P = 40`.
-/

namespace Submission.Obl.k4_conditional_common_affine_field

open MeasureTheory

theorem uniformGridField : UniformGridField := by
  refine ⟨40, by norm_num, ?_⟩
  intro Ω _ μ _ W t b₁ b₂ F rowOpts colOpts B ω E u hB hω hE hωP hW ht hb₁ hb₂ hF hu1 hu2 hrel
    hbd hrowN hcolN hrowB hcolB hrowFit hcolFit hcell hmass
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ B := by linarith
  set n := ⌊B⌋₊ with hndef
  have hnB : (n : ℝ) ≤ B := Nat.floor_le hB0.le
  have hn1 : 1 ≤ n := Nat.le_floor (by norm_num; linarith)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hBinv : 0 < B⁻¹ := inv_pos.mpr hB0
  have hupos : 0 < |u| := lt_of_lt_of_le hBinv hu1
  have hu : u ≠ 0 := fun h => by rw [h, abs_zero] at hupos; exact lt_irrefl _ hupos
  have hinvu : 1 / |u| ≤ B := by
    rw [div_le_iff₀ hupos]
    have := mul_le_mul_of_nonneg_left hu1 hB0.le
    rw [mul_inv_cancel₀ hB0.ne'] at this
    linarith
  -- powers of `B`
  have hpow : ∀ a b : ℕ, a ≤ b → B ^ a ≤ B ^ b := fun a b hab => pow_le_pow_right₀ hB1 hab
  have h2pow : ∀ k : ℕ, (2 : ℝ) ^ k ≤ B ^ k := fun k => pow_le_pow_left₀ (by norm_num) hB k
  have hBpos : ∀ k : ℕ, 0 < B ^ k := fun k => pow_pos hB0 k
  -- the anchor gap
  set γ := gridGap B⁻¹ n B B with hγdef
  have hm₂ : 1 / B ^ 3 ≤ B⁻¹ / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (hBpos 3) (by positivity)]
    have : (n : ℝ) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hn0.le hnB 2
    calc 1 * (n : ℝ) ^ 2 ≤ B ^ 2 := by linarith
      _ = B⁻¹ * B ^ 3 := by field_simp
  have hγlow : 1 / (384 * B ^ 11) ≤ γ := by
    rw [hγdef, gridGap]
    have h1 : (1 / B ^ 3) ^ 2 ≤ (B⁻¹ / (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hm₂ 2
    calc 1 / (384 * B ^ 11) = (1 / B ^ 3) ^ 2 / (384 * B ^ 2 * B ^ 3) := by field_simp
      _ ≤ (B⁻¹ / (n : ℝ) ^ 2) ^ 2 / (384 * B ^ 2 * B ^ 3) := by gcongr
  have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγlow
  have hinvγ : 1 / γ ≤ 384 * B ^ 11 := by
    rw [div_le_iff₀ hγpos]
    rw [div_le_iff₀ (by positivity)] at hγlow
    linarith
  have h384 : (384 : ℝ) ≤ B ^ 9 := le_trans (by norm_num) (h2pow 9)
  have hωγ : ω ≤ γ := by
    refine le_trans hωP (le_trans ?_ hγlow)
    rw [one_div]
    apply inv_anti₀ (by positivity)
    calc 384 * B ^ 11 ≤ B ^ 9 * B ^ 11 := by gcongr
      _ = B ^ 20 := by ring
      _ ≤ B ^ 40 := hpow 20 40 (by norm_num)
  have hωB : ω ≤ B := by
    refine le_trans hωP ?_
    calc (B ^ 40)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hB1)
      _ ≤ B := hB1
  obtain ⟨β, c, W', hW'm, hW'W, hβ, hc, hmass', hfit⟩ :=
    grid_common_field μ W hW t b₁ b₂ F ht hb₁ hb₂ hF rowOpts colOpts (ω := ω) (u := u) (B := B)
      (E := E) (κ := B) (m := B⁻¹) (n := n) hω hu hB1 hE hB0 hBinv hn1 hωB hrel
      (fun p hp => ⟨(hbd p hp).1, (hbd p hp).2.1, (hbd p hp).2.2.1⟩)
      (fun j => Nat.le_floor (hrowN j)) (fun j => Nat.le_floor (hcolN j)) hrowB hcolB hrowFit
      hcolFit hcell hmass hωγ
  refine ⟨β, c, W', hW'm, hW'W, ?_, ?_, ?_, ?_⟩
  · -- mass
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmass'
    rw [gridMass]
    have h1 : (1 / B ^ 3) ^ 3 ≤ (B⁻¹ / (n : ℝ) ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hm₂ 3
    have h512 : (512 : ℝ) ≤ B ^ 9 := le_trans (by norm_num) (h2pow 9)
    calc (B ^ 40)⁻¹ ≤ 1 / (512 * B ^ 15) := by
          rw [one_div]
          apply inv_anti₀ (by positivity)
          calc 512 * B ^ 15 ≤ B ^ 9 * B ^ 15 := by gcongr
            _ = B ^ 24 := by ring
            _ ≤ B ^ 40 := hpow 24 40 (by norm_num)
      _ = (1 / B ^ 3) ^ 3 / (512 * B ^ 2 * B ^ 4) := by field_simp
      _ ≤ (B⁻¹ / (n : ℝ) ^ 2) ^ 3 / (512 * B ^ 2 * B ^ 4) := by gcongr
  · -- coefficients
    intro k
    refine le_trans (hβ k) ?_
    have h1 : 1 + 1 / |u| ≤ 2 * B := by linarith
    have h2 : 1 + 1 / γ ≤ 385 * B ^ 11 := by
      have : 1 ≤ B ^ 11 := one_le_pow₀ hB1
      linarith
    calc 12 * B ^ 3 * (1 + 1 / |u|) * (1 + 1 / γ) ≤ 12 * B ^ 3 * (2 * B) * (385 * B ^ 11) := by
          gcongr
      _ = 9240 * B ^ 15 := by ring
      _ ≤ B ^ 14 * B ^ 15 := by
          gcongr
          exact le_trans (by norm_num) (h2pow 14)
      _ = B ^ 29 := by ring
      _ ≤ B ^ 40 := hpow 29 40 (by norm_num)
  · -- the constant
    exact le_trans hc (by simpa using hpow 1 40 (by norm_num))
  · -- the fits
    have herr : gridErr E ω u B γ ≤ B ^ 40 * (E + ω) := by
      rw [gridErr]
      have hBω : 4 * B * ω / |u| ≤ 4 * B ^ 2 * ω := by
        rw [div_le_iff₀ hupos]
        have : 1 ≤ B * |u| := by
          have := mul_le_mul_of_nonneg_left hu1 hB0.le
          rwa [mul_inv_cancel₀ hB0.ne'] at this
        nlinarith [mul_nonneg (mul_nonneg hB0.le hB0.le) hω.le]
      have hu3 : |u| + 3 * B ≤ 4 * B := by linarith
      have hstep : 2 * (2 * E + 4 * B * ω / |u|) * (|u| + 3 * B) / γ ≤
          2 * (2 * E + 4 * B ^ 2 * ω) * (4 * B) * (384 * B ^ 11) := by
        rw [div_eq_mul_one_div]
        gcongr
      have hB12 : 1 ≤ B ^ 12 := one_le_pow₀ hB1
      calc 3 * E + 2 * (2 * E + 4 * B * ω / |u|) * (|u| + 3 * B) / γ
          ≤ 3 * E + 2 * (2 * E + 4 * B ^ 2 * ω) * (4 * B) * (384 * B ^ 11) := by linarith
        _ = 3 * E + 6144 * B ^ 12 * E + 12288 * B ^ 14 * ω := by ring
        _ ≤ 18435 * B ^ 14 * E + 18435 * B ^ 14 * ω := by
            have hB1214 : B ^ 12 ≤ B ^ 14 := hpow 12 14 (by norm_num)
            have hB014 : 1 ≤ B ^ 14 := one_le_pow₀ hB1
            nlinarith
        _ = 18435 * B ^ 14 * (E + ω) := by ring
        _ ≤ B ^ 15 * B ^ 14 * (E + ω) := by
            gcongr
            exact le_trans (by norm_num) (h2pow 15)
        _ = B ^ 29 * (E + ω) := by ring
        _ ≤ B ^ 40 * (E + ω) :=
            mul_le_mul_of_nonneg_right (hpow 29 40 (by norm_num)) (by positivity)
    intro p hp
    obtain ⟨h1, h2⟩ := hfit p hp
    refine ⟨le_trans (le_of_eq ?_) (h1.trans herr), h2.trans herr⟩
    simp only [bilEval]

end Submission.Obl.k4_conditional_common_affine_field
