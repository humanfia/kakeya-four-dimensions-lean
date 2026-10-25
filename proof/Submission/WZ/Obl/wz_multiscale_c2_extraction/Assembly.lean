-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Assembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.LocalGridLinearity
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.ZoomBridge

/-!
# From local grid linearity to the frozen `W` examples

The frozen premise of o105 is the example class with slope clause `QL3` (a 1-Lipschitz slope
bounded by 3 on `[-1,1]`), and the frozen conclusion the class with slope clause `QW` (a `C²`
slope whose value and first two derivatives are at most `δ ^ (-η)` everywhere). Both are
`Reg.ExF` shapes. The analytic chain ported from o062/x0309 turns `LocalGridLinearity σ` into
`PowerApproximation σ`; here the last step stops at the `W` examples (no normalization).
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction

open Set Metric MeasureTheory
open scoped ENNReal
open Reg

/-- The slope clause of the frozen premise of o105. -/
def QL3 (_η _δ : ℝ) (n : ℕ) (_Y : Fin n → Set Reg.Space) (f : ℝ → ℝ) : Prop :=
  LipschitzWith 1 f ∧ ∀ z : ℝ, z ∈ Icc (-1) 1 → |f z| ≤ 3

/-- `PowerApproximation` turns the bounded Lipschitz examples into the `W` examples. -/
theorem exF_W_of_powerApproximation {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hA : PowerApproximation σ)
    (hL : ExF QL3 σ) : ExF QW σ := by
  intro ε d₀ hε hd₀
  let κ := min (ε / 4) (1 / 4)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκe : κ ≤ ε / 4 := min_le_left _ _
  have hκ1 : κ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨η, d₁, hη, hηκ, hd₁, happrox⟩ := hA κ hκ hκ1
  have hgap : 0 < ε - (η + κ) := by linarith
  obtain ⟨d₂, hd₂, hconstant⟩ := cut_le_one hgap 18
  obtain ⟨d₃, hd₃, hcompact⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff hκ
      (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, hD, hS, hC, hV, f, P, ⟨hf, hfb⟩, hg, hP, hn, ho,
      hl⟩ := hL η (min d₀ (min d₁ (min d₂ d₃))) hη
      (lt_min hd₀ (lt_min hd₁ (lt_min hd₂ hd₃)))
  have hfamily : ExtremalFamily σ η δ n x v Y := ⟨hD, strong_of_flat hS, hC, hV⟩
  have hgrains : Grains σ δ (δ ^ (-η)) v Y f P := ⟨hg, hP, hn, ho, hl⟩
  have hδ1 : δ ≤ 1 := by linarith
  have hδd₀ : δ ≤ d₀ := hδd.trans (min_le_left _ _)
  have hδd₁ : δ ≤ d₁ := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd₂ : δ ≤ d₂ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd₃ : δ ≤ d₃ := hδd.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Z, g, hZY, hZm, hmass, hgs, hgb, hgf⟩ :=
    happrox δ hδ hδd₁ hδ100 n x v Y f P hfamily hf hfb hgrains
  have hcover : 18 * δ ^ (-(η + κ)) ≤ δ ^ (-ε) := by
    have heq : δ ^ (-(η + κ)) = δ ^ (ε - (η + κ)) * δ ^ (-ε) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    rw [heq, ← mul_assoc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (hconstant δ hδ hδd₂) (Real.rpow_nonneg hδ.le (-ε))
  obtain ⟨K, hKZ, hKF, hKG⟩ := compact_power_slope_transfer
    (a := κ) (b := κ) hδ hδ1 hκ.le hσ0 hσ1 (by linarith) (by linarith)
    hcover (hcompact δ hδ hδd₃) hfamily hgrains hZY hZm hmass hgf
  have hpow : δ ^ (-κ) ≤ δ ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  exact ⟨δ, hδ, hδd₀, hδ100, n, x, v, K, hKF.1, flat_of_strong hKF.2.1, hKF.2.2.1,
    hKF.2.2.2, g, P, ⟨hgs, fun z => ⟨(hgb z).1.trans hpow, (hgb z).2.1.trans hpow,
      (hgb z).2.2.trans hpow⟩⟩, hKG.1, hKG.2.1, hKG.2.2.1, hKG.2.2.2.1, hKG.2.2.2.2⟩

/-- The whole analytic side: local grid linearity at `σ` upgrades the bounded Lipschitz
examples to the `W` examples. -/
theorem exF_W_of_localGridLinearity {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (h : LocalGridLinearity σ)
    (hL : ExF QL3 σ) : ExF QW σ :=
  exF_W_of_powerApproximation hσ0.le hσ1.le
    (powerApproximation_of_singleScaleLinearity hσ0 hσ1
      (singleScaleLinearity_of_localGridLinearity h)) hL

end WangZahlLot.Obl.wz_multiscale_c2_extraction
