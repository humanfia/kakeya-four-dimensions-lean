import Submission.Obl.k4_wide_three_layer_scalar_inputs.Parameters
import Submission.Obl.k4_wide_three_layer_scalar_inputs.InheritedBridge
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.IndexFacts
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.Blocks
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortDefs
import Submission.Obl.k4_horizontal_supercritical_three_projections.RawIndex

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory Set Filter
open Inherited.Native Inherited.Core

variable {α : Type} [MeasurableSpace α]

/-- Only original hypotheses at the fixed range of resolutions used by
the comparison. The original laws and assignment sets stay unchanged. -/
structure ComparisonEnvironment (cfg : Data α) (k : ℕ) (s u M Rcap : ℝ) : Prop where
  blocks : BlocksAt cfg.comparisonData k s Rcap
  caps : ∀ sp : ℝ, 0 ≤ sp → sp ≤ s + u →
    JointCapAt (cfg.μ k) (cfg.π k) (cfg.b k) (cfg.N k) (cfg.K k) cfg.d (2 * M) sp M
  measurable : Measurable (cfg.b k)
  rho_le : cfg.ρ k ≤ cfg.μ k
  finite : IsFiniteMeasure (cfg.μ k)
  prior_prob : IsProbabilityMeasure (cfg.ν k)
  palette_prob : IsProbabilityMeasure (cfg.π k)
  horizontal : ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀)
  length : cfg.N k ^ (-cfg.κ * s) / cfg.K k ≤ slotLen cfg.comparisonData k s ∧
    slotLen cfg.comparisonData k s ≤ cfg.K k * cfg.N k ^ (-cfg.κ * s)

/-- All-rate preparation and caps supply this environment at one fixed
range, chosen before the projected loss. -/
theorem eventually_comparison_environment {cfg : Data α} (hv : cfg.Valid)
    {buffer : ℝ} (hb : 100 < buffer)
    (p : Parameters cfg.d cfg.κ cfg.U cfg.e₀ buffer) :
    ∃ Rcap : ℝ, 1 < Rcap ∧ ∀ᶠ k in atTop,
      ComparisonEnvironment cfg k p.s p.u p.M Rcap := by
  have hM : 0 < p.M := p.M_pos (by linarith)
  have hs : 0 < p.s := p.s_pos
  have hsu : 0 < p.s + p.u := by linarith [p.u_pos]
  have hMi : 0 < p.M⁻¹ := inv_pos.mpr hM
  have hsi : 0 < p.s⁻¹ := inv_pos.mpr hs
  let Rcap := 2 + 2 * p.M + (p.s + p.u) + p.M⁻¹ + p.s⁻¹
  have hR : 1 < Rcap := by dsimp [Rcap]; linarith
  have hR0 : 0 < Rcap := by linarith
  have hRM : Rcap⁻¹ ≤ p.M := by
    apply (inv_le_comm₀ hR0 hM).mpr
    dsimp [Rcap]
    linarith
  have hRs : Rcap⁻¹ ≤ p.s := by
    apply (inv_le_comm₀ hR0 hs).mpr
    dsimp [Rcap]
    linarith
  have hRr : Rcap⁻¹ ≤ 2 * p.M := by linarith
  have hrR : 2 * p.M ≤ Rcap := by dsimp [Rcap]; linarith
  have hMR : p.M ≤ Rcap := by linarith
  have hspR : p.s + p.u ≤ Rcap := by dsimp [Rcap]; linarith
  have hpsU : p.s ≤ cfg.U := by linarith [p.su_U, p.u_pos]
  refine ⟨Rcap, hR, ?_⟩
  filter_upwards [blocksAt_eventually hv.comparisonData hR,
    jointCapAt_eventually cfg.comparisonData hv.comparisonData hR,
    index_facts cfg.comparisonData hv.comparisonData] with k hB hcap hf
  have hblock := hB p.s hRs hpsU
  obtain ⟨hmeas, hρμ, hfin, -, hhor, -⟩ := hf
  obtain ⟨-, hν, hπ, -⟩ := hv.basic k
  refine {
    blocks := hblock
    caps := fun sp hsp0 hsp => hcap (2 * p.M) sp p.M hRr hrR hsp0 (hsp.trans hspR) hRM hMR
    measurable := hmeas
    rho_le := hρμ
    finite := hfin
    prior_prob := hν
    palette_prob := hπ
    horizontal := hhor
    length := ?_ }
  have h := Submission.Obl.k4_horizontal_supercritical_three_projections.block_length_bounds
    (show 0 < cfg.N k by linarith [hv.scale k]) (hv.subpower.1 k)
    hblock.T_lo hblock.T_hi
  simpa only [slotLen, zpow_neg, zpow_natCast, neg_mul] using h

end Submission.Obl.k4_wide_three_layer_scalar_inputs
