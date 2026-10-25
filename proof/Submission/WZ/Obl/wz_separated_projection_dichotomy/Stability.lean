-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Stability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Quantization
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RealCover

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem power_slack {ε R T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 1 ≤ R) (hT : 0 ≤ T) (hTR : T ≤ 17 * R)
    (hlarge : 153 ≤ R ^ (ε / 2)) :
    T ^ (1 - ε) ≤ R ^ (1 - ε / 2) / 9 := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have h17 : (17 : ℝ) ^ (1 - ε) ≤ 17 := by
    calc (17 : ℝ) ^ (1 - ε) ≤ 17 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 17 := Real.rpow_one _
  have hprod : 153 * R ^ (1 - ε) ≤ R ^ (1 - ε / 2) := by
    have h := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hRpos.le (1 - ε))
    rw [← Real.rpow_add hRpos] at h
    convert h using 1 <;> congr 1 <;> ring
  calc T ^ (1 - ε) ≤ (17 * R) ^ (1 - ε) :=
      Real.rpow_le_rpow hT hTR (sub_nonneg.mpr hε1)
    _ = (17 : ℝ) ^ (1 - ε) * R ^ (1 - ε) := Real.mul_rpow (by norm_num) hRpos.le
    _ ≤ 17 * R ^ (1 - ε) :=
      mul_le_mul_of_nonneg_right h17 (Real.rpow_nonneg hRpos.le _)
    _ ≤ R ^ (1 - ε / 2) / 9 := by linarith

theorem exists_stability_cutoff {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → 153 ≤ δ ^ (-(η * ε / 2)) := by
  let s : ℝ := η * ε / 2
  have hs : 0 < s := by dsimp [s]; positivity
  let d : ℝ := (1 / 153 : ℝ) ^ s⁻¹
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min 1 d, lt_min zero_lt_one hd, min_le_left _ _, ?_⟩
  intro δ hδ hδ₀
  have hδd : δ ≤ d := hδ₀.trans (min_le_right _ _)
  have hp : δ ^ s ≤ (1 / 153 : ℝ) := by
    calc δ ^ s ≤ d ^ s := Real.rpow_le_rpow hδ.le hδd hs.le
      _ = (1 / 153 : ℝ) := Real.rpow_inv_rpow (by norm_num) hs.ne'
  change 153 ≤ δ ^ (-s)
  rw [Real.rpow_neg hδ.le]
  have hpos : 0 < δ ^ s := Real.rpow_pos_of_pos hδ s
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith

/-- Projection gain is stable under the `8δ` dot-product error of the finite
model, after reserving half the epsilon exponent. -/
theorem ProjectionGain.of_approximation {δ η ε : ℝ} {Q Q' : Set Triple}
    (h : ProjectionGain δ η (ε / 2) Q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : 153 ≤ δ ^ (-(η * ε / 2)))
    (happrox : ∀ p ∈ Q, ∃ q ∈ Q', dist (dotValue p) (dotValue q) ≤ 8 * δ) :
    ProjectionGain δ η ε Q' := by
  obtain ⟨ρ, a, L, hδρ, hL, hcover⟩ := h
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have hpow : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hη)
  have hρL : ρ ≤ L := by nlinarith
  have hLpos : 0 < L := hρ.trans_le hρL
  have hratio : δ ^ (-η) ≤ L / ρ := (le_div_iff₀ hρ).mpr hL
  have hR : 1 ≤ L / ρ := hpow.trans hratio
  have hlarge : 153 ≤ (L / ρ) ^ (ε / 2) := by
    calc 153 ≤ δ ^ (-(η * ε / 2)) := hsmall
      _ = (δ ^ (-η)) ^ (ε / 2) := by
        rw [← Real.rpow_mul hδ.le]
        congr 1
        ring
      _ ≤ (L / ρ) ^ (ε / 2) :=
        Real.rpow_le_rpow (by positivity) hratio (by positivity)
  have hT : 0 ≤ (L + 16 * δ) / ρ := by positivity
  have hTR : (L + 16 * δ) / ρ ≤ 17 * (L / ρ) := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hρ]
    linarith [hδρ.trans hρL]
  have hpower := power_slack hε hε1 hR hT hTR hlarge
  have hclose : ∀ t ∈ Set.Icc a (a + L) ∩ DotSet Q,
      ∃ u ∈ Set.Icc (a - 8 * δ) ((a - 8 * δ) + (L + 16 * δ)) ∩ DotSet Q',
        dist t u ≤ 8 * ρ := by
    rintro t ⟨ht, p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := happrox p hp
    have hdist : |dotValue p - dotValue q| ≤ 8 * δ := by
      simpa only [Real.dist_eq] using hpq
    have hbounds := abs_le.mp hdist
    change a ≤ dotValue p ∧ dotValue p ≤ a + L at ht
    refine ⟨dotValue q, ⟨⟨?_, ?_⟩, q, hq, rfl⟩, ?_⟩
    · linarith
    · linarith
    · exact hpq.trans (mul_le_mul_of_nonneg_left hδρ (by norm_num))
  refine ⟨ρ, a - 8 * δ, L + 16 * δ, hδρ, ?_, ?_⟩
  · linarith
  · exact (hcover.transfer_close hclose).weaken hpower

end WangZahlLot.Obl.wz_separated_projection_dichotomy
