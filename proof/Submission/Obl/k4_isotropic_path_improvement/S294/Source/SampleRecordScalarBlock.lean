-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleRecordScalarBlock, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeOriginalSourceBudgets

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open scoped ENNReal

noncomputable section

/-- Exact cut, original pure-cap and conditional palette fields of
the record block, at the actual front entropy and native coefficient power. -/
theorem sample_record_scalar_block
    (tune : Tuning) {N κ source κ₁ d₁ precision loss gain L δ₀ front divisor gap : ℝ} {Ep m C : ℕ}
    (hv : NativeDesign.Valid κ₁ d₁ precision loss)
    (hbudget : tune.budget κ₁ d₁ Ep precision loss=NativeDesign.budget κ₁ d₁ Ep precision loss)
    (hN : 1 ≤ N) (hgain : 0 < gain) (hL : 0 < L)
    (hgainCap : gain ≤ gainCap tune κ₁ d₁ Ep precision loss)
    (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ)) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100)
    (hδtol : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain)
    (hC : (C:ℝ) ≤ windowOf tune κ₁ d₁ Ep precision loss gain*(m:ℝ)+1)
    (_hfront : 0 < front) (hdivisor : 1 ≤ divisor) (hdivisorMax : divisor ≤ 5000)
    (hκ : 1 ≤ κ) (hκN : κ ≤ N^gap) (hsourceN : source ≤ N^gap)
    (hgap : gap ≤ (NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L))/1000000)
    (hlarge : 20000 ≤ N^((NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L))/1000000)) :
    let h := NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L)
    let internal := tune.budget κ₁ d₁ Ep precision loss*(loss*gain*L/((Ep:ℝ)+1))/divisor
    let entropy := entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L)
    let cut := N^(-RecordBudgets.cutExponent front internal)
    let Kcap := N^(h/1000)
    let chi := NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*L)
    0 < cut ∧ 0 < Kcap ∧ 0 ≤ chi ∧
      512*(max κ source)^2*κ*4^d₁*
        N^(2*(δ₀*L)+(tauOf tune δ₀ L front+2*δ₀*L)+tauOf tune δ₀ L front) ≤ Kcap ∧
      4*625*((8*N^entropy)/cut)*Kcap ≤ N^h ∧
      (4:ENNReal)*(ENNReal.ofReal ((8*N^entropy)/cut)/ENNReal.ofReal cut) ≤ ENNReal.ofReal (N^h) := by
  have hExponents := native_design_original_source_exponents tune hv hbudget hgain hL hδ0 hδtol hdivisor
  have hv0 := hv
  obtain ⟨hd0,hd1,hκ₁,hκ₁1,hprecision,hloss,_hloss1⟩ := hv0
  let h := NativeDesign.coefficientCoeff κ₁ d₁ Ep precision loss*(gain*L)
  let display := loss*gain*L/((Ep:ℝ)+1)
  let internal := tune.budget κ₁ d₁ Ep precision loss*display/divisor
  let entropy := entropyOf C m (ueOf tune κ₁ d₁ Ep precision loss gain δ₀ L)
  let b := RecordBudgets.cutExponent front internal
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hB := tune.budget_pos κ₁ d₁ Ep precision loss
  have hdisplay : 0 < display := by dsimp only [display]; positivity
  have hdivisor0 : 0 < divisor := zero_lt_one.trans_le hdivisor
  have hinternal : 0 < internal := by dsimp only [internal]; positivity
  have hEntropy : entropy ≤ internal/4 := front_entropy_le_internal_quarter
    (mul_nonneg hB.le hdisplay.le) hdivisor0 hdivisorMax
    (front_entropy_le_internal_power tune hκ₁ hκ₁1 hd0 hd1 hprecision hloss hgain hL.le hgainCap
      hm hgm hδ hC)
  have hb : 64*b ≤ internal := by
    dsimp only [b,RecordBudgets.cutExponent]
    linarith only [min_le_right front internal]
  have htau : tauOf tune δ₀ L front ≤ δ₀*L := min_le_left _ _
  have hRecord := native_original_record_envelope_bound hN hExponents.1 hgap hκ hκN hsourceN
    hExponents.2.2 htau hd1.le hlarge
  have hPalette := native_original_palette_power_budgets hN hExponents.1 hlarge hExponents.2.1
    hEntropy hb (Real.rpow_nonneg hNp.le (h/1000)) le_rfl
  have hChi : 0 ≤ NativeDesign.auxiliaryChiCoeff κ₁ d₁ Ep precision loss*(gain*L) :=
    mul_nonneg (NativeDesign.auxiliaryChiCoeff_pos κ₁ d₁ hloss).le (mul_nonneg hgain.le hL.le)
  exact ⟨Real.rpow_pos_of_pos hNp _,Real.rpow_pos_of_pos hNp _,hChi,(by simpa only [mul_assoc] using hRecord),hPalette.1,hPalette.2⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
