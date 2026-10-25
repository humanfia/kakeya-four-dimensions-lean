-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordWindowRoom, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFamily
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRecordAccuracy

/-!
# The room of the record family in the window (session x1082)

`record_window_room`: with the concrete native depth (`tune.depth = NativeDesign.depth`), the
window `C ≥ windowOf · m`, the core family margin `g = familyMarginOf κ₁ δ₀ ub m` and the family
`nfam = C - g + 1`, the record accuracy `accuracy = nativeRecordAccuracyCoeff · gain` fits both
room conditions of x1095's `sample_record_geometry_in_family`, uniformly in the ancestor level `i`:

* `(2 accuracy + 4 gain)/κ₁ ≤ s (i + C) - s i` (the full window);
* `accuracy + 2 gain ≤ s (i + nfam - 1) - s i` (the family keeps all but `g ≤ C/2` levels).

The accuracy is at most `2 D gain` (`native_record_accuracy_le_depth`), the window at least
`1024 D gain m/κ₁` and the margin at most `m gain/(40 κ₁) + 2` (`familyMargin_le_window`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The scalar error of the core family margin is at most `gain/40` (as inside
`familyMargin_le_window`). -/
theorem familyMargin_error_le (tune : Tuning) {κ₁ d₁ precision loss gain δ₀ : ℝ} {Ep : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hδ0 : 0 ≤ δ₀) (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) (hδg : δ₀ ≤ gain / 100) :
    3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
      ubOf tune κ₁ d₁ Ep precision loss gain + 2 * δ₀ ≤ gain / 40 := by
  set F := (censusFixedPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set dp := (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ)
  set ub := ubOf tune κ₁ d₁ Ep precision loss gain
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
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have h1 : 3 * δ₀ * dp ≤ 60 * (δ₀ * (F + 1)) := by nlinarith
  have h2 : 60 * (δ₀ * (F + 1)) ≤ gain / 10000 := by
    have := hdr
    have h3 : loss * gain / ((Ep : ℝ) + 1) / 640000 ≤ gain / 640000 := by
      apply div_le_div_of_nonneg_right hD (by norm_num)
    nlinarith
  have h4 : ub ≤ gain / 4096 := hur.trans (div_le_div_of_nonneg_right hD (by norm_num))
  linarith

/-- **The room of the record family.** -/
theorem record_window_room (tune : Tuning) {κ₁ d₁ precision loss gain δ₀ : ℝ} {Ep m C i : ℕ}
    {s : ℕ → ℝ}
    (hdepth : tune.depth κ₁ d₁ Ep precision loss = NativeDesign.depth κ₁ d₁ Ep precision loss)
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hgain : 0 < gain) (hδ0 : 0 ≤ δ₀) (hm : 0 < m) (hs : ∀ l, s l = ((l : ℝ) + 1) / m)
    (hslackC : censusSlack ≤ tune.slack)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) (hδg : δ₀ ≤ gain / 100)
    (hgm : 8 ≤ gain * (m : ℝ))
    (hC : windowOf tune κ₁ d₁ Ep precision loss gain * m ≤ C) :
    familyMarginOf κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss gain) m ≤ C ∧
      (2 * (nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss * gain) + 4 * gain) / κ₁ ≤
        s (i + C) - s i ∧
      nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss * gain + 2 * gain ≤
        s (i + (C - familyMarginOf κ₁ δ₀ (ubOf tune κ₁ d₁ Ep precision loss gain) m + 1) - 1) -
          s i := by
  obtain ⟨hd0, hd1, hκ, hκ1, hprec, hloss, hloss1⟩ := hv
  have hv' : NativeDesign.Valid κ₁ d₁ precision loss := ⟨hd0, hd1, hκ, hκ1, hprec, hloss, hloss1⟩
  set D := NativeDesign.depth κ₁ d₁ Ep precision loss with hD
  set coef := nativeRecordAccuracyCoeff κ₁ d₁ Ep precision loss with hcoefDef
  set ub := ubOf tune κ₁ d₁ Ep precision loss gain with hub
  set g := familyMarginOf κ₁ δ₀ ub m with hg
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hD1 : 1 ≤ D := NativeDesign.one_le_depth κ₁ d₁ Ep precision loss
  obtain ⟨hcoef0, hcoef⟩ := native_record_accuracy_le_depth Ep hv'
  rw [← hcoefDef, ← hD] at hcoef
  rw [← hcoefDef] at hcoef0
  -- the window is at least `1024 D gain m/κ₁`
  have hX4 : (4 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by
    have : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
    nlinarith
  have hW : 1024 * D * gain * m / κ₁ ≤ (C : ℝ) := by
    refine le_trans ?_ hC
    unfold windowOf
    rw [hdepth, div_mul_eq_mul_div]
    have hd1' : 0 < 1 - d₁ := by linarith
    have hDgm : 0 ≤ D * gain * m := by positivity
    calc 1024 * D * gain * m / κ₁ ≤
          1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * D * m / κ₁ := by
          apply div_le_div_of_nonneg_right _ hκ.le
          have e1 : 1024 * D * gain * m = 1024 * (D * gain * m) := by ring
          have e2 : 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * D * m =
              1024 * (((Ep : ℝ) + 1) * precision + 3) * (D * gain * m) := by ring
          rw [e1, e2]
          have : (1 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by linarith
          have := mul_le_mul_of_nonneg_right this hDgm
          linarith
      _ ≤ 1024 * (((Ep : ℝ) + 1) * precision + 3) * gain * D * m / ((1 - d₁) * κ₁) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          have : (1 - d₁) * κ₁ ≤ 1 * κ₁ := mul_le_mul_of_nonneg_right (by linarith) hκ.le
          linarith
  -- the margin
  have hmg : 1 / (m : ℝ) ≤ gain / κ₁ := by
    rw [div_le_div_iff₀ hmR hκ]
    nlinarith
  have hgC : g ≤ C := familyMargin_le_window tune hκ hκ1 hd0 hd1 hprec hloss hloss1 hgain hδ0 hm
    hslackC hδ hδg hmg hC
  refine ⟨hgC, ?_, ?_⟩
  · -- the full window
    rw [hs, hs]
    have hgap : ((((i + C : ℕ) : ℝ) + 1) / m - ((i : ℝ) + 1) / m) = (C : ℝ) / m := by
      push_cast; ring
    rw [hgap, le_div_iff₀ hmR]
    have h1 : (2 * (coef * gain) + 4 * gain) / κ₁ ≤ 8 * D * gain / κ₁ := by
      apply div_le_div_of_nonneg_right _ hκ.le
      nlinarith
    have h2 : 8 * D * gain / κ₁ * m ≤ 1024 * D * gain * m / κ₁ := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hκ.le
      have : 0 ≤ D * gain * m := by positivity
      nlinarith
    calc (2 * (coef * gain) + 4 * gain) / κ₁ * m ≤ 8 * D * gain / κ₁ * m :=
          mul_le_mul_of_nonneg_right h1 hmR.le
      _ ≤ 1024 * D * gain * m / κ₁ := h2
      _ ≤ C := hW
  · -- the family keeps all but `g` levels
    have hidx : i + (C - g + 1) - 1 = i + (C - g) := by omega
    rw [hidx, hs, hs]
    have hgap : ((((i + (C - g) : ℕ) : ℝ) + 1) / m - ((i : ℝ) + 1) / m) = ((C : ℝ) - g) / m := by
      rw [Nat.cast_add, Nat.cast_sub hgC]; ring
    rw [hgap, le_div_iff₀ hmR]
    -- `g ≤ m gain/(40 κ₁) + 2 ≤ m gain/κ₁`
    have hgle : (g : ℝ) ≤ (m : ℝ) * gain / κ₁ := by
      have hgw := familyMargin_le_window tune hκ hκ1 hd0 hd1 hprec hloss hloss1 hgain hδ0 hm
        hslackC hδ hδg hmg hC
      -- the ceiling bound of the margin
      have hX : 3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
          ub + 2 * δ₀ ≤ gain / 40 :=
        familyMargin_error_le tune hκ hκ1 hloss hloss1 hgain hδ0 hslackC hδ hδg
      have hX0 : 0 ≤ 3 * δ₀ * (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) +
          ub + 2 * δ₀ := by
        have hu0 : 0 ≤ ub := by
          rw [hub]; unfold ubOf
          have := tune.budget_pos κ₁ d₁ Ep precision loss
          positivity
        positivity
      have hceil : (g : ℝ) ≤ (m : ℝ) * (3 * δ₀ *
          (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub + 2 * δ₀) / κ₁ +
            2 := by
        rw [hg]; unfold familyMarginOf; push_cast
        have := (Nat.ceil_lt_add_one (show 0 ≤ (m : ℝ) * (3 * δ₀ *
          (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub + 2 * δ₀) / κ₁
            by positivity)).le
        linarith
      have h1 : (m : ℝ) * (3 * δ₀ *
          (deepPowerOf FixedSourcePowers.coreRadius FixedSourcePowers.jet : ℝ) + ub + 2 * δ₀) / κ₁ ≤
          (m : ℝ) * (gain / 40) / κ₁ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hX hmR.le) hκ.le
      have h2 : (2 : ℝ) ≤ (m : ℝ) * gain / (4 * κ₁) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h3 : (m : ℝ) * (gain / 40) / κ₁ + (m : ℝ) * gain / (4 * κ₁) ≤ (m : ℝ) * gain / κ₁ := by
        have e1 : (m : ℝ) * (gain / 40) / κ₁ = (m : ℝ) * gain / κ₁ / 40 := by ring
        have e2 : (m : ℝ) * gain / (4 * κ₁) = (m : ℝ) * gain / κ₁ / 4 := by
          rw [mul_comm 4 κ₁, ← div_div]
        have : 0 ≤ (m : ℝ) * gain / κ₁ := by positivity
        rw [e1, e2]; linarith
      linarith
    have hW' : 1024 * ((m : ℝ) * gain / κ₁) * D ≤ (C : ℝ) := by
      calc 1024 * ((m : ℝ) * gain / κ₁) * D = 1024 * D * gain * m / κ₁ := by ring
        _ ≤ C := hW
    set P := (m : ℝ) * gain / κ₁ with hPdef
    have hP0 : 0 ≤ P := by positivity
    have hQ0 : 0 ≤ gain * (m : ℝ) := by positivity
    have hQP : gain * (m : ℝ) ≤ P := by
      rw [hPdef, le_div_iff₀ hκ]
      have := mul_le_mul_of_nonneg_left hκ1 hQ0
      linarith
    have h1 : (coef * gain + 2 * gain) * m = (coef + 2) * (gain * (m : ℝ)) := by ring
    have h2 : (coef + 2) * (gain * (m : ℝ)) ≤ (2 * D + 2) * (gain * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ0
    have h3 : (2 * D + 2) * (gain * (m : ℝ)) ≤ 4 * D * (gain * (m : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hQ0
    have h4 : 4 * D * (gain * (m : ℝ)) ≤ 4 * D * P :=
      mul_le_mul_of_nonneg_left hQP (by positivity)
    have hPD : P ≤ P * D := le_mul_of_one_le_right hP0 hD1
    have e5 : 4 * D * P = 4 * (P * D) := by ring
    have e6 : 1024 * P * D = 1024 * (P * D) := by ring
    have hPD0 : 0 ≤ P * D := by positivity
    rw [h1]
    linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
