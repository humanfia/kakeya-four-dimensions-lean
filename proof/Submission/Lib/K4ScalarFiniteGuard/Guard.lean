/-
Adapted from: here:o093
Original proofs by session x0535 in this LOT workspace. The scalar atlas
interface was written in the same o093 tree by x0364; this package retains
its literal fields while requiring only the sampling hypotheses used here.
-/

import Submission.Lib.K4ScalarFiniteGuard.KnownLimits

/-!
The fixed-complexity finite-sample horizon exclusion. Thickness and
observation exponents may vary with the original exact sample. Compactness
and actual power-grid list transport turn any infinitely recurring output
into a genuine known atlas at the limiting exponents.
-/

set_option autoImplicit false

namespace Submission.Lib.K4ScalarFiniteGuard

open Set Filter
open scoped Topology

/-- Excluding genuine known improvements gives an eventual exclusion of
all fixed-complexity charts with vanishing losses, uniformly in their
actual thickness, knowledge depth, horizon and smaller loss budgets. -/
theorem uniform_finiteSampleGuard (p : Code) (hp : Sampling p) (B : ℕ) (hB : 1 ≤ B)
    (κ gain margin : ℝ) (hgain : 0 < gain) (hmargin : 0 < margin)
    (loss : ℕ → ℝ) (hloss : Tendsto loss atTop (𝓝 0))
    (hexclude : ∀ r b h : ℝ, 0 ≤ r → r < L p → r ≤ b → b ≤ L p →
      h ≤ κ * r - gain / 2 → ¬ Known p r b h) :
    ∀ᶠ k in atTop, ∀ r b h ε : ℝ, 0 ≤ r → r ≤ L p - margin →
      r ≤ b → b ≤ L p → h ≤ κ * r - gain → ε ≤ loss k →
      ¬ Chart p B r b h ε false k := by
  classical
  by_contra hno
  have hbad : ∃ᶠ k in atTop, ∃ r b h ε : ℝ,
      0 ≤ r ∧ r ≤ L p - margin ∧ r ≤ b ∧ b ≤ L p ∧
      h ≤ κ * r - gain ∧ ε ≤ loss k ∧ Chart p B r b h ε false k := by
    apply (Filter.not_eventually.1 hno).mono
    intro k hk
    push Not at hk
    exact hk
  obtain ⟨sample, hsample, houtputs⟩ := Filter.extraction_of_frequently_atTop hbad
  choose depth knowledge cost oldLoss hd₀ hdmax hdk hkmax hcost hLoss hchart using houtputs
  let region : Set (ℝ × ℝ) := Icc (0 : ℝ) (L p - margin) ×ˢ Icc (0 : ℝ) (L p)
  have hcompact : IsCompact region := isCompact_Icc.prod isCompact_Icc
  have hmem (n : ℕ) : (depth n, knowledge n) ∈ region :=
    ⟨⟨hd₀ n, hdmax n⟩, ⟨(hd₀ n).trans (hdk n), hkmax n⟩⟩
  obtain ⟨z, hz, ψ, hψ, hzlim⟩ := hcompact.tendsto_subseq hmem
  have hdlim : Tendsto (fun k => depth (ψ k)) atTop (𝓝 z.1) := by
    exact ((continuous_fst.tendsto z).comp hzlim).congr' (Eventually.of_forall fun _ => rfl)
  have hklim : Tendsto (fun k => knowledge (ψ k)) atTop (𝓝 z.2) := by
    exact ((continuous_snd.tendsto z).comp hzlim).congr' (Eventually.of_forall fun _ => rfl)
  have hdkLimit : z.1 ≤ z.2 :=
    le_of_tendsto_of_tendsto' hdlim hklim (fun k => hdk (ψ k))
  have hboundLimit : Tendsto (fun k => κ * depth (ψ k) - gain) atTop
      (𝓝 (κ * z.1 - gain)) := (hdlim.const_mul κ).sub_const gain
  have hnonneg (k : ℕ) : 0 ≤ κ * depth (ψ k) - gain := by
    have hcost₀ := chart_horizon_nonneg p B (sample (ψ k))
      (depth (ψ k)) (knowledge (ψ k)) (cost (ψ k)) (oldLoss (ψ k)) false
      ((by norm_num : (1 : ℝ) < 2).trans_le (hp.1 _)) (hchart (ψ k))
    exact hcost₀.trans (hcost (ψ k))
  have hlimNonneg : 0 ≤ κ * z.1 - gain :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hboundLimit hnonneg
  let h := κ * z.1 - gain / 2
  have hh : 0 ≤ h := by dsimp only [h]; linarith
  let actualSample := sample ∘ ψ
  have hactual : Tendsto actualSample atTop atTop :=
    hsample.tendsto_atTop.comp hψ.tendsto_atTop
  have hactualLoss : Tendsto (fun k => loss (actualSample k)) atTop (𝓝 0) :=
    hloss.comp hactual
  have hactualChart (k : ℕ) :
      Chart p B (depth (ψ k)) (knowledge (ψ k)) (cost (ψ k))
        (loss (actualSample k)) false (actualSample k) := by
    exact chart_mono p B (actualSample k) (depth (ψ k)) (knowledge (ψ k))
      (cost (ψ k)) (cost (ψ k)) (oldLoss (ψ k)) (loss (actualSample k)) false
      ((by norm_num : (1 : ℝ) ≤ 2).trans (hp.1 _)) le_rfl (hLoss (ψ k)) (hchart (ψ k))
  have hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cost (ψ k) ≤ h + ε := by
    intro ε hε
    have hsmall : ∀ᶠ k in atTop, κ * depth (ψ k) - gain < h + ε :=
      hboundLimit.eventually_lt tendsto_const_nhds (by dsimp only [h]; linarith)
    exact hsmall.mono fun k hk => (hcost (ψ k)).trans hk.le
  have hknown := known_of_varying_charts p hp B hB actualSample hactual z.1 z.2 h hh
    (fun k => depth (ψ k)) (fun k => knowledge (ψ k)) (fun k => cost (ψ k))
    (fun k => loss (actualSample k)) hdlim hklim hactualLoss hupper
    (Eventually.of_forall hactualChart).frequently
  exact hexclude z.1 z.2 h hz.1.1 (by linarith [hz.1.2]) hdkLimit hz.2.2 le_rfl hknown


end Submission.Lib.K4ScalarFiniteGuard
