-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The core depth family of a sample (session x1088).

The family is ALL levels `i, …, i + C - g` below the ancestor level `i`, where the margin
`g = familyMarginOf κ₁ δ₀ ub m = ⌈m (3 δ₀ deepPowerOf + ub + 2 δ₀)/κ₁⌉ + 1` is fixed before the
sample:
* `familyMargin_spec`: `3 δ₀ deepPowerOf + ub + 2 δ₀ ≤ κ₁ (s b - s a)` whenever `a + g ≤ b`
  (the pre-sample deep margin of the census, `Source.CensusChoices.deep_margin`);
* `deepPower_le`: `deepPowerOf R J ≤ 20 (censusFixedPowerOf R J + 1)`;
* `familyMargin_le_window`: `g ≤ C` from the grid, the tolerance, the slack and the window. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRates

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The margin of the core family below the end of the window. -/
def familyMarginOf (κ₁ δ₀ ub : ℝ) (m : ℕ) : ℕ :=
  ⌈(m : ℝ) * (3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
    ub + 2 * δ₀) / κ₁⌉₊ + 1

theorem familyMargin_spec {κ₁ δ₀ ub : ℝ} {m : ℕ} {s : ℕ → ℝ} (hκ : 0 < κ₁) (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hX : 0 ≤ 3 * δ₀ *
      (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub + 2 * δ₀)
    {a b : ℕ} (hab : a + familyMarginOf κ₁ δ₀ ub m ≤ b) :
    3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub + 2 * δ₀ ≤
      κ₁ * (s b - s a) := by
  set X := 3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub +
    2 * δ₀
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hg : (m : ℝ) * X / κ₁ ≤ (familyMarginOf κ₁ δ₀ ub m : ℝ) := by
    unfold familyMarginOf; push_cast
    have := Nat.le_ceil ((m : ℝ) * X / κ₁)
    linarith
  have hba : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ (b : ℝ) - a := by
    have : ((a + familyMarginOf κ₁ δ₀ ub m : ℕ) : ℝ) ≤ b := by exact_mod_cast hab
    push_cast at this; linarith
  have hsd : s b - s a = ((b : ℝ) - a) / m := by rw [hs, hs]; ring
  rw [hsd]
  have h1 : (m : ℝ) * X / κ₁ ≤ ((b : ℝ) - a) := hg.trans hba
  rw [div_le_iff₀ hκ] at h1
  rw [mul_div_assoc', le_div_iff₀ hmR]
  linarith

theorem deepPower_le (R J : ℕ) : deepPowerOf R J ≤ 20 * (censusFixedPowerOf R J + 1) := by
  unfold deepPowerOf censusFixedPowerOf
  nlinarith [Nat.zero_le (R * J), Nat.zero_le ((2 * R + 32) * ⌈Parent.ParentSource.coreRowC₀⌉₊)]

/-- **The margin fits in the window.** -/
theorem familyMargin_le_window (tune : Tuning) {κ₁ d₁ precision loss gain δ₀ : ℝ} {Ep m C : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀) (hm : 0 < m)
    (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) (hδg : δ₀ ≤ gain / 100)
    (hmg : 1 / (m : ℝ) ≤ gain / κ₁)
    (hC : windowOf tune κ₁ d₁ Ep precision loss gain * m ≤ C) :
    familyMarginOf κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss gain) m ≤ C := by
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set dp := (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set ub := ubOf tune κ₁ d₁ Ep precision loss gain
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hEp : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by have := (Nat.cast_nonneg Ep : (0 : ℝ) ≤ Ep); linarith
  have hD : loss * gain / ((Ep : ℝ) + 1) ≤ gain := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hdp : dp ≤ 20 * (F + 1) := by
    have := deepPower_le FixedSourcePowers.coreRadius FixedSourcePowers.jet
    have h' : ((deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℕ) : ℝ) ≤
        ((20 * (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet + 1) : ℕ) : ℝ) :=
      by exact_mod_cast this
    push_cast at h'; exact h'
  have hdr := delta_rate tune hloss hgain hδ0 hslackC hδ
  have hur := ub_rate tune hκ hκ1 hloss hgain (d₁ := d₁) (Ep := Ep) (precision := precision)
  have hu0 : 0 ≤ ub := by
    simp only [ub]; unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hF : 0 ≤ F := Nat.cast_nonneg _
  -- `X ≤ gain/40`
  have hX : 3 * δ₀ * dp + ub + 2 * δ₀ ≤ gain / 40 := by
    have h1 : 3 * δ₀ * dp ≤ 60 * (δ₀ * (F + 1)) := by nlinarith
    have h2 : 60 * (δ₀ * (F + 1)) ≤ gain / 10000 := by
      have := hdr
      have h3 : loss * gain / ((Ep : ℝ) + 1) / 640000 ≤ gain / 640000 := by
        apply div_le_div_of_nonneg_right hD (by norm_num)
      nlinarith
    have h4 : ub ≤ gain / 4096 := hur.trans (div_le_div_of_nonneg_right hD (by norm_num))
    linarith
  have hX0 : 0 ≤ 3 * δ₀ * dp + ub + 2 * δ₀ := by
    have : 0 ≤ dp := Nat.cast_nonneg _
    positivity
  -- `g ≤ m X/κ₁ + 2 ≤ windowOf m`
  have hg : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ (m : ℝ) * (3 * δ₀ * dp + ub + 2 * δ₀) / κ₁ + 2 := by
    unfold familyMarginOf; push_cast
    have := (Nat.ceil_lt_add_one (show 0 ≤ (m : ℝ) * (3 * δ₀ * dp + ub + 2 * δ₀) / κ₁ by
      positivity)).le
    linarith
  have hmgk : 1 ≤ (m : ℝ) * gain / κ₁ := by
    rw [le_div_iff₀ hκ]
    rw [div_le_div_iff₀ hmR hκ] at hmg
    linarith
  have hW : 1024 * ((m : ℝ) * gain / κ₁) ≤ windowOf tune κ₁ d₁ Ep precision loss gain * m := by
    unfold windowOf
    have hdep := tune.one_le_depth κ₁ d₁ Ep precision loss
    have hP : (4 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by nlinarith
    have hd1 : 0 < 1 - d₁ := by linarith
    have hd2 : 1 - d₁ ≤ 1 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hA : (m : ℝ) * gain / κ₁ * ((1 - d₁) * κ₁) ≤ (m : ℝ) * gain := by
      have e : (m : ℝ) * gain / κ₁ * ((1 - d₁) * κ₁) = (m : ℝ) * gain * (1 - d₁) := by
        field_simp
      rw [e]
      have : 0 ≤ (m : ℝ) * gain := by positivity
      nlinarith
    have hB : 1024 * ((m : ℝ) * gain) ≤
        1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * tune.depth κ₁ d₁ Ep precision loss * m := by
      have : 0 ≤ (m : ℝ) * gain := by positivity
      have h1 : (1 : ℝ) ≤ (((Ep : ℝ) + 1) * precision + 3) * tune.depth κ₁ d₁ Ep precision loss := by
        nlinarith
      nlinarith
    nlinarith
  have hfin : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ C := by
    have hmX : (m : ℝ) * (3 * δ₀ * dp + ub + 2 * δ₀) / κ₁ ≤ (m : ℝ) * gain / κ₁ / 40 := by
      rw [div_div, div_le_div_iff₀ hκ (by positivity)]
      have h40 : (3 * δ₀ * dp + ub + 2 * δ₀) * 40 ≤ gain := by linarith
      have h' := mul_le_mul_of_nonneg_left h40 (mul_nonneg hmR.le hκ.le)
      calc (m : ℝ) * (3 * δ₀ * dp + ub + 2 * δ₀) * (κ₁ * 40)
          = ((m : ℝ) * κ₁) * ((3 * δ₀ * dp + ub + 2 * δ₀) * 40) := by ring
        _ ≤ ((m : ℝ) * κ₁) * gain := h'
        _ = (m : ℝ) * gain * κ₁ := by ring
    linarith
  exact_mod_cast hfin

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
