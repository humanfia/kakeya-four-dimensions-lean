-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleWindow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The window inequalities of the list fits (session x1088).

Pre-sample comparisons, with `Y = m gain/κ₁ ≥ 1`, `X₀ = (Ep+1) precision + 3`, the depth at least
`graphLowerCoeff` (`NativeDesign.depth`), the window `windowOf m ≤ C` and the family margin
`g = familyMarginOf … ≤ m gain/(40 κ₁) + 2`:
* `familyMargin_le_real`: the margin bound;
* `listA_window`: `m (2δ₀ + (3δ₀ Fc + ub + 100 ρc + gl gain) + gain) + 1 < nfamAt`;
* `listB_window`: `c + m (2δ₀ + (3δ₀ Fc + ub + 3 X₀ gain/κ₁) + gain) + 1 < nfamAt`;
* `band_rate`: `gl gain ≤ 1/4`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFits
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleAtNumerics

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

section Window

variable (tune : Tuning) {κ₁ d₁ precision loss e0 δ₀ : ℝ} {Ep m C : ℕ}

/-- The family margin, in reals. -/
theorem familyMargin_le_real (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (he0 : 0 < e0)
    (hδ0 : 0 ≤ δ₀) (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0))
    (hδg : δ₀ ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / 100) :
    (familyMarginOf κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss
        (gainOf tune κ₁ d₁ Ep precision loss e0)) m : ℝ) ≤
      (m : ℝ) * gainOf tune κ₁ d₁ Ep precision loss e0 / (40 * κ₁) + 2 := by
  set gain := gainOf tune κ₁ d₁ Ep precision loss e0
  have hg : 0 < gain := gainOf_pos hκ hd₁ hprec hloss he0
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set dp := (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set ub := ubOf tune κ₁ d₁ Ep precision loss gain
  have hEp : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by have := (Nat.cast_nonneg Ep : (0 : ℝ) ≤ Ep); linarith
  have hD : loss * gain / ((Ep : ℝ) + 1) ≤ gain := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hdp : dp ≤ 20 * (F + 1) := by
    have := deepPower_le FixedSourcePowers.coreRadius FixedSourcePowers.jet
    have h' : ((deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℕ) : ℝ) ≤
        ((20 * (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet + 1) : ℕ) :
          ℝ) := by exact_mod_cast this
    push_cast at h'; exact h'
  have hdr := delta_rate tune hloss hg hδ0 hslackC hδ
  have hur := ub_rate tune hκ hκ1 hloss hg (d₁ := d₁) (Ep := Ep) (precision := precision)
  have hu0 : 0 ≤ ub := by
    simp only [ub]; unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hdp0 : 0 ≤ dp := Nat.cast_nonneg _
  have hX : 3 * δ₀ * dp + ub + 2 * δ₀ ≤ gain / 40 := by
    have h1 : 3 * δ₀ * dp ≤ 60 * (δ₀ * (F + 1)) := by nlinarith
    have h2 : 60 * (δ₀ * (F + 1)) ≤ gain / 10000 := by
      have h3 : loss * gain / ((Ep : ℝ) + 1) / 640000 ≤ gain / 640000 :=
        div_le_div_of_nonneg_right hD (by norm_num)
      nlinarith
    have h4 : ub ≤ gain / 4096 := hur.trans (div_le_div_of_nonneg_right hD (by norm_num))
    linarith
  have hX0 : 0 ≤ 3 * δ₀ * dp + ub + 2 * δ₀ := by positivity
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold familyMarginOf; push_cast
  have h := (Nat.ceil_lt_add_one (show 0 ≤ (m : ℝ) * (3 * δ₀ * dp + ub + 2 * δ₀) / κ₁ by
    positivity)).le
  have hmX : (m : ℝ) * (3 * δ₀ * dp + ub + 2 * δ₀) / κ₁ ≤ (m : ℝ) * gain / (40 * κ₁) := by
    rw [div_le_div_iff₀ hκ (by positivity)]
    have := mul_le_mul_of_nonneg_left hX (mul_nonneg hmR hκ.le)
    nlinarith
  linarith

/-- The window in units of `Y = m gain/κ₁`: `windowOf m ≥ 1024 X₀ depth Y`. -/
theorem window_ge (hκ : 0 < κ₁) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision)
    (hloss : 0 < loss) (he0 : 0 < e0) :
    1024 * (((Ep : ℝ) + 1) * precision + 3) * tune.depth κ₁ d₁ Ep precision loss *
        ((m : ℝ) * gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁) ≤
      windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m := by
  set gain := gainOf tune κ₁ d₁ Ep precision loss e0
  set D := tune.depth κ₁ d₁ Ep precision loss
  have hg : 0 < gain := gainOf_pos hκ hd₁ hprec hloss he0
  have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hd1 : 0 < 1 - d₁ := by linarith
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hP : (0 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by
    have : (0 : ℝ) ≤ precision := by linarith
    positivity
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : windowOf tune κ₁ d₁ Ep precision loss gain * m =
      (1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * D * m) / ((1 - d₁) * κ₁) := by
    unfold windowOf; ring
  have e2 : 1024 * (((Ep : ℝ) + 1) * precision + 3) * D * ((m : ℝ) * gain / κ₁) =
      (1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * D * m) / κ₁ := by ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The root's list fits in the window.** -/
theorem listA_window (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (he0 : 0 < e0)
    (hδ0 : 0 ≤ δ₀) (hm : 0 < m) (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0))
    (hδg : δ₀ ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / 100)
    (hgm : 8 ≤ gridFineOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m)
    (hmg : 1 / (m : ℝ) ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁)
    (hdepth : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤ tune.depth κ₁ d₁ Ep precision loss)
    (hCge : windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C) :
    (m : ℝ) * (2 * δ₀ + (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
        ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) +
        100 * (3 * δ₀ * (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
          ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) + 1 / (m : ℝ)) +
        NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * gainOf tune κ₁ d₁ Ep precision loss e0) +
        gainOf tune κ₁ d₁ Ep precision loss e0) + 1 <
      (nfamAt κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0))
        m C : ℝ) := by
  set gain := gainOf tune κ₁ d₁ Ep precision loss e0
  set ub := ubOf tune κ₁ d₁ Ep precision loss gain
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set gl := NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision
  have hg : 0 < gain := gainOf_pos hκ hd₁ hprec hloss he0
  have hEp : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by have := (Nat.cast_nonneg Ep : (0 : ℝ) ≤ Ep); linarith
  have hD : loss * gain / ((Ep : ℝ) + 1) ≤ gain := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hdr := delta_rate tune hloss hg hδ0 hslackC hδ
  have hur := ub_rate tune hκ hκ1 hloss hg (d₁ := d₁) (Ep := Ep) (precision := precision)
  have hgr := grid_rate tune hloss hg hgm
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hu0 : 0 ≤ ub := by
    simp only [ub]; unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hgl : 1000 ≤ gl := graphLower_ge hκ hd₀ hd₁ hprec
  -- the rates in units of `gain`
  have hδF : 3 * δ₀ * F ≤ gain / 100000 := by
    have h1 : δ₀ * (F + 1) ≤ gain / 640000 :=
      hdr.trans (div_le_div_of_nonneg_right hD (by norm_num))
    nlinarith
  have hub : ub ≤ gain / 4096 := hur.trans (div_le_div_of_nonneg_right hD (by norm_num))
  have hm1 : 1 / (m : ℝ) ≤ gain / 4096 := hgr.trans (div_le_div_of_nonneg_right hD (by norm_num))
  have hrate : 2 * δ₀ + (3 * δ₀ * F + ub + 100 * (3 * δ₀ * F + ub + 1 / (m : ℝ)) + gl * gain) +
      gain ≤ gain * (gl + 2) := by nlinarith
  -- `Y = m gain/κ₁ ≥ 1`
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set Y := (m : ℝ) * gain / κ₁ with hY
  have hY1 : 1 ≤ Y := by
    rw [hY, le_div_iff₀ hκ]
    rw [div_le_div_iff₀ hmR hκ] at hmg
    linarith
  have hmgY : (m : ℝ) * gain ≤ Y := by
    rw [hY, le_div_iff₀ hκ]
    have : 0 ≤ (m : ℝ) * gain := by positivity
    nlinarith
  -- the margin and the window
  have hgm' := familyMargin_le_real tune (m := m) hκ hκ1 hd₀ hd₁ hprec hloss hloss1 he0 hδ0
    hslackC hδ hδg
  have hgY : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ Y / 40 + 2 := by
    have e : (m : ℝ) * gain / (40 * κ₁) = Y / 40 := by rw [hY]; field_simp
    rw [← e]; exact hgm'
  have hwin := window_ge tune (Ep := Ep) (m := m) hκ hd₀ hd₁ hprec hloss he0
  rw [← hY] at hwin
  have hP : (4 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by
    have : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
    nlinarith
  have hCY : 4096 * gl * Y ≤ (C : ℝ) := by
    have h1 : 4096 * gl * Y ≤ 1024 * (((Ep : ℝ) + 1) * precision + 3) *
        tune.depth κ₁ d₁ Ep precision loss * Y := by
      have hY0 : 0 ≤ Y := by linarith
      have hgl0 : 0 ≤ gl := by linarith
      have : 4 * gl ≤ (((Ep : ℝ) + 1) * precision + 3) * tune.depth κ₁ d₁ Ep precision loss := by
        nlinarith
      nlinarith
    linarith
  have hglY : 1000 * Y ≤ gl * Y := mul_le_mul_of_nonneg_right hgl (by linarith)
  -- the margin is at most `C`
  have hgC : familyMarginOf κ₁ δ₀ ub m ≤ C := by
    have : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ C := by linarith
    exact_mod_cast this
  have hnfam : (nfamAt κ₁ δ₀ ub m C : ℝ) = (C : ℝ) + 1 - (familyMarginOf κ₁ δ₀ ub m : ℝ) := by
    unfold nfamAt
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hnfam]
  have hgain0 : 0 ≤ gain * (gl + 2) := by positivity
  have h1 : (m : ℝ) * (2 * δ₀ + (3 * δ₀ * F + ub + 100 * (3 * δ₀ * F + ub + 1 / (m : ℝ)) +
      gl * gain) + gain) ≤ Y * (gl + 2) := by
    calc (m : ℝ) * (2 * δ₀ + (3 * δ₀ * F + ub + 100 * (3 * δ₀ * F + ub + 1 / (m : ℝ)) +
          gl * gain) + gain) ≤ (m : ℝ) * (gain * (gl + 2)) :=
          mul_le_mul_of_nonneg_left hrate hmR.le
      _ = ((m : ℝ) * gain) * (gl + 2) := by ring
      _ ≤ Y * (gl + 2) := mul_le_mul_of_nonneg_right hmgY (by linarith)
  have e : Y * (gl + 2) = gl * Y + 2 * Y := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- **The children's list fits in the window.** -/
theorem listB_window (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (he0 : 0 < e0)
    (hδ0 : 0 ≤ δ₀) (hm : 0 < m) (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0))
    (hδg : δ₀ ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / 100)
    (hmg : 1 / (m : ℝ) ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁)
    (hCge : windowOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) * m ≤ C) :
    (childOffset κ₁ Ep precision (gainOf tune κ₁ d₁ Ep precision loss e0) m : ℝ) +
        (m : ℝ) * (2 * δ₀ + (3 * δ₀ *
        (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
        ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0) +
        3 * (((Ep : ℝ) + 1) * precision + 3) * gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁) +
        gainOf tune κ₁ d₁ Ep precision loss e0) + 1 <
      (nfamAt κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss (gainOf tune κ₁ d₁ Ep precision loss e0))
        m C : ℝ) := by
  set gain := gainOf tune κ₁ d₁ Ep precision loss e0
  set ub := ubOf tune κ₁ d₁ Ep precision loss gain
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set X₀ := ((Ep : ℝ) + 1) * precision + 3
  have hg : 0 < gain := gainOf_pos hκ hd₁ hprec hloss he0
  have hEp : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by have := (Nat.cast_nonneg Ep : (0 : ℝ) ≤ Ep); linarith
  have hD : loss * gain / ((Ep : ℝ) + 1) ≤ gain := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hdr := delta_rate tune hloss hg hδ0 hslackC hδ
  have hur := ub_rate tune hκ hκ1 hloss hg (d₁ := d₁) (Ep := Ep) (precision := precision)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hu0 : 0 ≤ ub := by
    simp only [ub]; unfold ubOf
    have := tune.budget_pos κ₁ d₁ Ep precision loss
    positivity
  have hδF : 3 * δ₀ * F ≤ gain / 100000 := by
    have h1 : δ₀ * (F + 1) ≤ gain / 640000 :=
      hdr.trans (div_le_div_of_nonneg_right hD (by norm_num))
    nlinarith
  have hub : ub ≤ gain / 4096 := hur.trans (div_le_div_of_nonneg_right hD (by norm_num))
  have hP : (4 : ℝ) ≤ X₀ := by
    have : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
    nlinarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set Y := (m : ℝ) * gain / κ₁ with hY
  have hY1 : 1 ≤ Y := by
    rw [hY, le_div_iff₀ hκ]
    rw [div_le_div_iff₀ hmR hκ] at hmg
    linarith
  have hmgY : (m : ℝ) * gain ≤ Y := by
    rw [hY, le_div_iff₀ hκ]
    have : 0 ≤ (m : ℝ) * gain := by positivity
    nlinarith
  -- the child offset
  have hco := childOffset_div_le (Ep := Ep) hκ hm hg hprec hmg
  have hcY : (childOffset κ₁ Ep precision gain m : ℝ) ≤ 2 * X₀ * Y := by
    rw [div_le_iff₀ hmR] at hco
    have e : 2 * X₀ * gain / κ₁ * m = 2 * X₀ * Y := by rw [hY]; ring
    linarith
  -- the rates: `m (...) ≤ Y (3 X₀ + 2)`
  have hrate : (m : ℝ) * (2 * δ₀ + (3 * δ₀ * F + ub + 3 * X₀ * gain / κ₁) + gain) ≤
      Y * (3 * X₀ + 2) := by
    have h1 : 2 * δ₀ + (3 * δ₀ * F + ub) + gain ≤ 2 * gain := by linarith
    have e : (m : ℝ) * (2 * δ₀ + (3 * δ₀ * F + ub + 3 * X₀ * gain / κ₁) + gain) =
        (m : ℝ) * (2 * δ₀ + (3 * δ₀ * F + ub) + gain) + 3 * X₀ * Y := by rw [hY]; ring
    rw [e]
    have h2 : (m : ℝ) * (2 * δ₀ + (3 * δ₀ * F + ub) + gain) ≤ 2 * ((m : ℝ) * gain) := by
      have := mul_le_mul_of_nonneg_left h1 hmR.le
      linarith
    nlinarith
  -- the margin and the window
  have hgm' := familyMargin_le_real tune (m := m) hκ hκ1 hd₀ hd₁ hprec hloss hloss1 he0 hδ0
    hslackC hδ hδg
  have hgY : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ Y / 40 + 2 := by
    have e : (m : ℝ) * gain / (40 * κ₁) = Y / 40 := by rw [hY]; field_simp
    rw [← e]; exact hgm'
  have hwin := window_ge tune (Ep := Ep) (m := m) hκ hd₀ hd₁ hprec hloss he0
  rw [← hY] at hwin
  have hD1 := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hCY : 1024 * X₀ * Y ≤ (C : ℝ) := by
    have h1 : 1024 * X₀ * Y ≤ 1024 * X₀ * tune.depth κ₁ d₁ Ep precision loss * Y := by
      have hY0 : 0 ≤ Y := by linarith
      have hX0 : 0 ≤ X₀ := by linarith
      have := mul_le_mul_of_nonneg_left hD1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 1024) hX0)
      nlinarith
    linarith
  have hXY : 4 * Y ≤ X₀ * Y := mul_le_mul_of_nonneg_right hP (by linarith)
  have hgC : familyMarginOf κ₁ δ₀ ub m ≤ C := by
    have : (familyMarginOf κ₁ δ₀ ub m : ℝ) ≤ C := by linarith
    exact_mod_cast this
  have hnfam : (nfamAt κ₁ δ₀ ub m C : ℝ) = (C : ℝ) + 1 - (familyMarginOf κ₁ δ₀ ub m : ℝ) := by
    unfold nfamAt
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hnfam]
  have e1 : Y * (3 * X₀ + 2) = 3 * (X₀ * Y) + 2 * Y := by ring
  have e2 : 2 * X₀ * Y = 2 * (X₀ * Y) := by ring
  have e3 : 1024 * X₀ * Y = 1024 * (X₀ * Y) := by ring
  linarith

/-- **The band rate**: `graphLowerCoeff gain ≤ 1/4`. -/
theorem band_rate (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1)
    (hprec : 1 ≤ precision) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (he0 : 0 < e0)
    (hdepth : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤ tune.depth κ₁ d₁ Ep precision loss) :
    NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * gainOf tune κ₁ d₁ Ep precision loss e0 ≤
      1 / 4 := by
  have hg := gain_scaled_le tune (Ep := Ep) hκ hd₀ hd₁ hprec hloss hloss1 he0
  have hg0 : 0 < gainOf tune κ₁ d₁ Ep precision loss e0 := gainOf_pos hκ hd₁ hprec hloss he0
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hP : (1 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by nlinarith
  have hgl : 0 ≤ NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision := by
    have := graphLower_ge (Ep := Ep) hκ hd₀ hd₁ hprec; linarith
  have h1 : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision * gainOf tune κ₁ d₁ Ep precision loss e0 ≤
      gainOf tune κ₁ d₁ Ep precision loss e0 *
        ((((Ep : ℝ) + 1) * precision + 3) * tune.depth κ₁ d₁ Ep precision loss) := by
    have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
    have h2 : NativeDesign.graphLowerCoeff κ₁ d₁ Ep precision ≤
        (((Ep : ℝ) + 1) * precision + 3) * tune.depth κ₁ d₁ Ep precision loss := by nlinarith
    nlinarith
  have h3 : (1 - d₁) ^ 2 * κ₁ ^ 2 / 2 ^ 48 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    have : (1 - d₁) ^ 2 ≤ 1 := by nlinarith
    have : κ₁ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  linarith

end Window

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
