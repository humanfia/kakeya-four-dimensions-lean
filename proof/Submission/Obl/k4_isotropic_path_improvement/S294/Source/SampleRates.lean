-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Pre-sample rate inequalities of the outer assembly (session x1088).

With `D = loss gain/(Ep+1)` (so `K = N^(D L)`), the grid facts (`δ₀ ≤ tolOf`,
`8 ≤ gridFineOf m`) and `censusSlack ≤ tune.slack`:
* `ub_rate`, `grid_rate`, `delta_rate`: `ub ≤ D/4096`, `1/m ≤ D/4096`,
  `δ₀ (Fc + 1) ≤ D/(640000)`;
* `brow_rate`: `72 δ₀ + 1806 (3 δ₀ Fc + ub + 1/m) + 18 ub ≤ (98/100) D` (the rate inequality of
  `eventually_brow_le`, with the census rate `ρc = 3 δ₀ Fc + ub + 1/m` of `censusK_le` and
  `eventually_geom_le`). -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.CensusEventual
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Window

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

section Rates

variable (tune : Tuning) {κ₁ d₁ precision loss gain δ₀ : ℝ} {Ep m : ℕ}

theorem ub_rate (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hloss : 0 < loss) (hgain : 0 < gain) :
    ubOf tune κ₁ d₁ Ep precision loss gain ≤ loss * gain / ((Ep : ℝ) + 1) / 4096 := by
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hEp : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have e : ubOf tune κ₁ d₁ Ep precision loss gain =
      κ₁ * tune.budget κ₁ d₁ Ep precision loss * (loss * gain / ((Ep : ℝ) + 1)) / 4096 := by
    unfold ubOf; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hκB : κ₁ * tune.budget κ₁ d₁ Ep precision loss ≤ 1 := by nlinarith
  have hD : 0 ≤ loss * gain / ((Ep : ℝ) + 1) := by positivity
  have := mul_le_mul_of_nonneg_right hκB hD
  linarith

theorem grid_rate (hloss : 0 < loss) (hgain : 0 < gain)
    (hgm : 8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss gain * m) :
    1 / (m : ℝ) ≤ loss * gain / ((Ep : ℝ) + 1) / 4096 := by
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hEp : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  unfold gridFineOf at hgm
  have hm : (0 : ℝ) < m := by
    by_contra h
    push Not at h
    have : (m : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg m)
    rw [this, mul_zero] at hgm
    linarith
  rw [div_le_iff₀ hm]
  have hlg : 0 < loss * gain / ((Ep : ℝ) + 1) := by positivity
  have e : tune.budget κ₁ d₁ Ep precision loss * loss * gain / (512 * ((Ep : ℝ) + 1)) * m =
      tune.budget κ₁ d₁ Ep precision loss * (loss * gain / ((Ep : ℝ) + 1)) * m / 512 := by
    field_simp
  rw [e] at hgm
  have hBD : tune.budget κ₁ d₁ Ep precision loss * (loss * gain / ((Ep : ℝ) + 1)) ≤
      loss * gain / ((Ep : ℝ) + 1) := by nlinarith
  have := mul_le_mul_of_nonneg_right hBD hm.le
  nlinarith

theorem delta_rate (hloss : 0 < loss) (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀)
    (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    δ₀ * ((censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + 1) ≤
      loss * gain / ((Ep : ℝ) + 1) / 640000 := by
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hEp : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have hS : 64 * (F + 1) ≤ tune.slack := hslackC
  have hS0 : 0 < tune.slack := by linarith
  unfold tolOf at hδ
  set D := loss * gain / ((Ep : ℝ) + 1)
  have hD : 0 < D := by positivity
  have e : tune.budget κ₁ d₁ Ep precision loss * loss * gain /
      (10000 * ((Ep : ℝ) + 1) * tune.slack) =
      tune.budget κ₁ d₁ Ep precision loss * D / (10000 * tune.slack) := by
    simp only [D]; field_simp
  rw [e] at hδ
  have hδ' : δ₀ ≤ D / (10000 * tune.slack) := by
    refine hδ.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    nlinarith
  have h1 : δ₀ * (F + 1) ≤ D / (10000 * tune.slack) * (F + 1) :=
    mul_le_mul_of_nonneg_right hδ' (by linarith)
  have h2 : D / (10000 * tune.slack) * (F + 1) ≤ D / 640000 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hS hD.le
    nlinarith
  linarith

/-- **The rate inequality of `eventually_brow_le`.** -/
theorem brow_rate (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hloss : 0 < loss) (hgain : 0 < gain)
    (hδ0 : 0 ≤ δ₀) (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hgm : 8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss gain * m) :
    72 * δ₀ + 1806 * (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
        ubOf tune κ₁ d₁ Ep precision loss gain + 1 / (m : ℝ)) +
      18 * ubOf tune κ₁ d₁ Ep precision loss gain ≤
      98 / 100 * (loss * gain / ((Ep : ℝ) + 1)) := by
  have hu := ub_rate tune hκ hκ1 hloss hgain (d₁ := d₁) (Ep := Ep) (precision := precision)
  have hg := grid_rate tune hloss hgain hgm
  have hd := delta_rate tune hloss hgain hδ0 hslackC hδ
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  set D := loss * gain / ((Ep : ℝ) + 1)
  have hD : 0 < D := by positivity
  have hu0 : 0 ≤ ubOf tune κ₁ d₁ Ep precision loss gain := by
    unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  -- `72 δ₀ + 5418 δ₀ F ≤ 5418 δ₀ (F + 1) ≤ 5418 D/640000`
  have h1 : 72 * δ₀ + 5418 * (δ₀ * F) ≤ 5418 * (δ₀ * (F + 1)) := by nlinarith
  nlinarith

end Rates

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
