import Submission.Obl.k4_scalar_guarded_entropic_path.ViewStage
import Submission.Obl.k4_scalar_guarded_entropic_path.StageEnvelope

/-! The original-unit payload gives every geometric field of the
canonical raw stage, with the actual allowance in its guard. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView

open MeasureTheory Set PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

variable {root final : Code} {D S₀ η : ℝ}

theorem toRawStage_geometry_good (a : OriginalView root final D S₀ η)
    (hz : Split.Exact final) (inner k M m : ℕ) (Mb : ℤ)
    {scale v δ ε buffer d κ R α : ℝ}
    (E : Set (Fin (Split.W final inner) × State)) (node : ℝ → Fin a.count)
    (layers : Fin a.count → Layer (Split.W a.parent (a.suffixChain.sample inner)))
    (hR : 1 < R) (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hscaleδ : scale ≤ δ)
    (hbuffer : 0 < buffer) (hbufferδ : buffer ≤ δ)
    (hM : 1 ≤ M) (hMp : Split.M a.parent ≤ M) (hDp : Split.D a.parent ≤ M)
    (hLp : Split.L a.parent ≤ (M : ℝ)) (hlength : scale * R < Split.L a.parent)
    (henvelope : PowerEnvelope (Code.N a.parent (a.suffixChain.sample inner))
      (Code.K a.parent (a.suffixChain.sample inner))
      (∑ g, ENNReal.ofReal (Code.weight a.parent (a.suffixChain.sample inner) g) *
        a.suffixChain.selectedWorldLaw inner E g univ) k a.count M scale v δ)
    (hlayers : ∀ j, a.OriginalLayerGood inner M ε v
      (Code.N a.parent (a.suffixChain.sample inner) ^ v)
      (Code.N a.parent (a.suffixChain.sample inner) ^ (scale * δ)) d κ
      (a.suffixChain.selectedWorldLaw inner E) j (layers j))
    (hnode : ∀ s : ℝ, R⁻¹ ≤ s → s ≤ R → |a.depth (node s) / scale - s| ≤ δ)
    (hguard : ∀ r h : ℝ, 0 ≤ r → r < Split.L a.parent → h ≤ κ * r - scale * buffer →
      ¬Split.Chart a.parent (2 ^ ((M + k + 1) ^ 2)) r (Split.L a.parent) h
        (Real.log ((Code.N a.parent (a.suffixChain.sample inner) ^ v *
          Real.log (Code.N a.parent (a.suffixChain.sample inner))) ^ (k + 1)) /
            Real.log (Code.N a.parent (a.suffixChain.sample inner)))
        false (a.suffixChain.sample inner)) :
    RawStage.GeometryGood
      (a.toRawStage inner scale (Code.N a.parent (a.suffixChain.sample inner) ^ v) buffer
        (Code.N a.parent (a.suffixChain.sample inner) ^ (scale * δ)) M ε E node layers m Mb α)
      d κ k R δ := by
  let N₀ := Code.N a.parent (a.suffixChain.sample inner)
  have hNtwo : 2 ≤ N₀ := a.parent_exact.1.1 (a.suffixChain.sample inner)
  have hN1 : 1 ≤ N₀ := by linarith
  have hN0 : 0 < N₀ := by linarith
  have hlog : Real.log N₀ ≠ 0 := (Real.log_pos (by linarith : 1 < N₀)).ne'
  have htolerance : Real.log (N₀ ^ v) / Real.log N₀ = v := by
    rw [Real.log_rpow hN0, mul_div_cancel_right₀ _ hlog]
  have hNren : 1 ≤ N₀ ^ scale := Real.one_le_rpow hN1 hscale.le
  refine
    { exact := a.parent_exact
      budgets := ⟨hscale, hscale1, henvelope.H_two, hbuffer, hM, hMp, hDp, hLp,
        henvelope.K_le, henvelope.count_le, henvelope.H_format, henvelope.H_B⟩
      scale_le := hscaleδ
      buffer_le := hbufferδ
      actual_le := henvelope.actual
      length_gt := hlength
      resolution_ge := henvelope.resolution
      B_ge_one := henvelope.B_one
      B_le := henvelope.B_le
      sigma_le := fun g => a.suffixChain.selectedWorldLaw_le hz inner E g
      sigma_mass := henvelope.mass_reserve
      layer_good := a.toRawStage_layer_good inner E node layers hscale htolerance hlayers
      node_round := ?_
      guard := ?_ }
  · intro s hs₁ hs₂
    change (N₀ ^ scale) ^ |a.depth (node s) / scale - s| ≤ N₀ ^ (scale * δ)
    calc
      _ ≤ (N₀ ^ scale) ^ δ := Real.rpow_le_rpow_of_exponent_le hNren (hnode s hs₁ hs₂)
      _ = _ := (Real.rpow_mul hN0.le scale δ).symm
  · intro r h hr₁ hr₂ hh
    change h ≤ κ * r - buffer at hh
    have hr0 : 0 ≤ r := (inv_nonneg.mpr (by linarith : 0 ≤ R)).trans hr₁
    have hscr : 0 ≤ scale * r := mul_nonneg hscale.le hr0
    have hscrL : scale * r < Split.L a.parent :=
      (mul_le_mul_of_nonneg_left hr₂ hscale.le).trans_lt hlength
    apply hguard (scale * r) (scale * h) hscr hscrL
    nlinarith only [hh, hscale]

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView
