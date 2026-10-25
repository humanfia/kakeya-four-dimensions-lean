import Submission.Obl.k4_oss_dyadic_reduction.Numerics
import Submission.Obl.k4_weighted_convex_tubes.SamplingAsymptotics

open Filter Set
open scoped Topology

namespace Submission.Obl.k4_oss_bad_direction_extraction

/-- A gap between real exponents absorbs any fixed multiplier. -/
theorem eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : b < a) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), C * δ ^ a ≤ δ ^ b := by
  filter_upwards [Submission.Obl.k4_oss_dyadic_reduction.eventually_small_power C
    (sub_pos.mpr hab), self_mem_nhdsWithin] with δ hh hδ
  have hδ : 0 < δ := hδ
  calc
    C * δ ^ a = (C * δ ^ (a - b)) * δ ^ b := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ 1 * δ ^ b := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hδ.le _)
    _ = δ ^ b := one_mul _

/-- One loss exponent and one scale cutoff satisfy all sampling and relation budgets. -/
theorem extraction_parameters {b η : ℝ} (hb : 0 < b) (hη : 0 < η) :
    ∃ θ r : ℝ, 0 < θ ∧ θ ≤ η ∧ 0 < r ∧ r ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ < r →
        δ ≤ 1 ∧ δ ^ θ ≤ 1 ∧
        16 * (δ ^ (-θ) * δ ^ b) ≤ δ ^ θ / 258 ∧
        (32 + 2 * δ ^ (-(η / 4))) * δ ^ (-θ) ≤ δ ^ (-η) * (δ ^ θ / 258) ∧
        16 * (δ⁻¹) ^ 2 ≤ Real.exp (δ ^ (-(η / 4)) / 2) ∧
        δ ^ η ≤ δ ^ θ / 20000 ∧
        20000 * δ ^ (-3 * θ) < δ ^ (-η) := by
  let θ : ℝ := min b η / 100
  have hθ : 0 < θ := div_pos (lt_min hb hη) (by norm_num)
  have hθb : 100 * θ ≤ b := by dsimp [θ]; linarith [min_le_left b η]
  have hθη : 100 * θ ≤ η := by dsimp [θ]; linarith [min_le_right b η]
  obtain ⟨rS, hrS, hsampling⟩ :=
    Submission.Obl.k4_weighted_convex_tubes.sampling_power_slack
      (τ := η / 4) (B := 4) (by positivity) (by norm_num)
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      4128 * δ ^ (b - θ) ≤ δ ^ θ ∧
      8772 * δ ^ (-(η / 4) - θ) ≤ δ ^ (θ - η) ∧
      20000 * δ ^ η ≤ δ ^ θ ∧
      40000 * δ ^ (-3 * θ) ≤ δ ^ (-η) := by
    filter_upwards [
      eventually_mul_rpow_le 4128 (a := b - θ) (b := θ) (by linarith),
      eventually_mul_rpow_le 8772 (a := -(η / 4) - θ) (b := θ - η) (by linarith),
      eventually_mul_rpow_le 20000 (a := η) (b := θ) (by linarith),
      eventually_mul_rpow_le 40000 (a := -3 * θ) (b := -η) (by linarith)]
      with δ h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r₀, hr₀, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨θ, min r₀ (min 1 rS), hθ, by linarith,
    lt_min hr₀ (lt_min zero_lt_one hrS), (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro δ hδ hδr
  have hδ1 : δ ≤ 1 := (hδr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδS : δ ≤ rS := (hδr.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨h1, h2, h3, h4⟩ := hsmall ⟨hδ, hδr.trans_le (min_le_left _ _)⟩
  have hL : 1 ≤ δ ^ (-(η / 4)) := by
    calc
      1 = δ ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ δ ^ (-(η / 4)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  refine ⟨hδ1, Real.rpow_le_one hδ.le hδ1 hθ.le, ?_, ?_, ?_, ?_, ?_⟩
  · have he : δ ^ (-θ) * δ ^ b = δ ^ (b - θ) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [he]
    linarith
  · have he : δ ^ (-(η / 4)) * δ ^ (-θ) = δ ^ (-(η / 4) - θ) := by
      rw [← Real.rpow_add hδ]
      congr 1
    have hf : δ ^ (-η) * δ ^ θ = δ ^ (θ - η) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    have hleft : (32 + 2 * δ ^ (-(η / 4))) * δ ^ (-θ) ≤
        34 * δ ^ (-(η / 4) - θ) := by
      rw [← he]
      nlinarith [Real.rpow_pos_of_pos hδ (-θ)]
    have hright : 34 * δ ^ (-(η / 4) - θ) ≤ δ ^ (-η) * (δ ^ θ / 258) := by
      rw [← mul_div_assoc, hf]
      linarith
    exact hleft.trans hright
  · have hs := (hsampling δ hδ hδS).2
    have hpow : δ ^ (-4 : ℝ) = (δ⁻¹) ^ 4 := by
      rw [Real.rpow_neg hδ.le, Real.rpow_ofNat, inv_pow]
    have hi : 1 ≤ δ⁻¹ := by
      rw [← one_div, le_div_iff₀ hδ]
      simpa using hδ1
    calc
      16 * (δ⁻¹) ^ 2 ≤ 16 * (δ⁻¹) ^ 4 := by
        nlinarith [sq_nonneg ((δ⁻¹) ^ 2 - 1)]
      _ ≤ Real.exp ((δ ^ (-(η / 4)) / 4) / 2) := by
        norm_num only [hpow] at hs ⊢
        exact hs
      _ ≤ Real.exp (δ ^ (-(η / 4)) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.rpow_pos_of_pos hδ (-(η / 4))]
  · linarith
  · exact lt_of_lt_of_le (by nlinarith [Real.rpow_pos_of_pos hδ (-3 * θ)]) h4

end Submission.Obl.k4_oss_bad_direction_extraction
