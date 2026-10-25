import Mathlib

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- Two small deletions retain half of a finite positive reference mass. -/
theorem source_two_deletions {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S1 S2 F : Set Ω} (hS21 : S2 ⊆ S1) (hS2m : MeasurableSet S2)
    (hFm : MeasurableSet F) (hfin : μ S1 ≠ ⊤) (hpos : 0 < μ.real S1)
    (hdel1 : μ.real (S1 \ S2) ≤ μ.real S1 / 4)
    (hdel2 : μ.real (S2 \ F) ≤ μ.real S1 / 4) :
    μ.real S1 / 2 ≤ μ.real (S2 ∩ F) ∧ 0 < μ.real (S2 ∩ F) := by
  have h1 := measureReal_sdiff (μ := μ) hS21 hS2m hfin
  have h2 := measureReal_inter_add_sdiff (μ := μ) (s := S2) hFm
    (measure_ne_top_of_subset hS21 hfin)
  constructor <;> linarith

/-- Convert the three original-law deletion costs to a real bound while retaining
the same full packet and the same original window reference. -/
theorem original_deletion_real_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S1 S2 P : Set Ω} (hSfin : μ S1 ≠ ⊤) (hPfin : μ P ≠ ⊤)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ a)
    (hdel : μ (S1 \ S2) ≤ ENNReal.ofReal a * μ P + ENNReal.ofReal b * μ S1 +
      ENNReal.ofReal c * μ P) :
    μ.real (S1 \ S2) ≤ 2 * a * μ.real P + b * μ.real S1 := by
  have hh : μ (S1 \ S2) ≤ ENNReal.ofReal a * μ P + ENNReal.ofReal b * μ S1 +
      ENNReal.ofReal a * μ P := hdel.trans
    (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl))
  have hr := ENNReal.toReal_mono (show ENNReal.ofReal a * μ P + ENNReal.ofReal b * μ S1 +
      ENNReal.ofReal a * μ P ≠ ⊤ by finiteness) hh
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at hr
  change μ.real (S1 \ S2) ≤ a * μ.real P + b * μ.real S1 + a * μ.real P at hr
  linarith only [hr]

/-- The supplied local floor is much smaller than the retained window mass. -/
theorem selection_mass_floor {m κ τ P R G : ℝ} (hm : 1 ≤ m) (hκ : 1 ≤ κ)
    (hτ : 0 < τ) (hP : 0 ≤ P) (hR : 0 < R)
    (hbudget : τ * (10 ^ 6 * (m + 1) ^ 2 * κ ^ 12) ≤ 1)
    (hfloor : (1 / (64 * m * κ ^ 2)) * P ≤ R) (hkeep : R / 2 ≤ G) :
    m * τ * P < G := by
  have hm0 : 0 < m := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκpow : κ ^ 2 ≤ κ ^ 12 := pow_le_pow_right₀ hκ (by norm_num)
  have hmm : m ^ 2 ≤ (m + 1) ^ 2 := by nlinarith
  have hcost : 128 * m ^ 2 * κ ^ 2 < 10 ^ 6 * (m + 1) ^ 2 * κ ^ 12 := by
    calc 128 * m ^ 2 * κ ^ 2 < 10 ^ 6 * m ^ 2 * κ ^ 2 :=
          mul_lt_mul_of_pos_right
            (mul_lt_mul_of_pos_right (by norm_num : (128 : ℝ) < 10 ^ 6)
              (sq_pos_of_pos hm0)) (sq_pos_of_pos hκ0)
      _ ≤ _ := by gcongr
  have hsmall : m * τ < 1 / (128 * m * κ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have hc := mul_lt_mul_of_pos_left hcost hτ
    nlinarith [hc, hbudget]
  by_cases hP0 : P = 0
  · rw [hP0, mul_zero]
    linarith
  · have hPpos : 0 < P := lt_of_le_of_ne hP (Ne.symm hP0)
    have hs := mul_lt_mul_of_pos_right hsmall hPpos
    have hf : (1 / (128 * m * κ ^ 2)) * P ≤ R / 2 := by
      convert div_le_div_of_nonneg_right hfloor (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
    exact hs.trans_le (hf.trans hkeep)

end

end Submission.Obl.k4_finite_affine_parent_sources
