import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.LayerBounds

/-! Every candidate retains original TRUE layers on the same reference
law, with all original assignments and witness sets unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path

open MeasureTheory Set PathGeometry PathGeometry.PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

namespace PathGeometry.OriginalView

variable {root final : Code} {D S₀ η : ℝ}

def OriginalLayerGood (a : OriginalView root final D S₀ η) (k M : ℕ)
    (ε v H B d κ : ℝ) (σ : Fin ((Split.W a.parent) (a.suffixChain.sample k)) → Measure Incidence)
    (j : Fin a.count) (F : Layer ((Split.W a.parent) (a.suffixChain.sample k))) : Prop :=
  Split.ChartData a.parent M (a.depth j) (Split.L a.parent) (a.time j + ε) v true
    (a.suffixChain.sample k) F.T F.n F.world F.block F.assignment F.witness
      F.u F.v F.width F.graph F.list ∧
    (∀ i, (H * (2 : ℝ) ^ F.T)⁻¹ ≤ F.width i) ∧
    (∀ g, σ g {z | ∃ i, F.world i = g ∧ z ∈ F.witness i}ᶜ = 0) ∧
    (Split.N a.parent) (a.suffixChain.sample k) ^
      |(Split.f a.parent) (a.depth j) - d * a.depth j| ≤ B ∧
    (Split.N a.parent) (a.suffixChain.sample k) ^ (κ * a.depth j) / B ≤ (2 : ℝ) ^ F.T ∧
    (2 : ℝ) ^ F.T ≤ B * (Split.N a.parent) (a.suffixChain.sample k) ^ (κ * a.depth j) ∧
    ∀ g, (σ g).map (pureObservation ((Split.N a.parent) (a.suffixChain.sample k)) (a.depth j)) ≤
      ENNReal.ofReal (B * (Split.N a.parent) (a.suffixChain.sample k) ^
        (-(Split.f a.parent) (a.depth j))) • (volume.prod Measure.count)

theorem exists_original_layers (a : OriginalView root final D S₀ η) (k M G : ℕ)
    (ε v u H B d κ gain β loss τ : ℝ)
    (P : (j : Fin a.count) → a.ChartAt ε k j)
    (hM : a.complexity ≤ M) (hMG : M ≤ G) (hεv : ε ≤ v) (hεloss : ε ≤ loss)
    (hH : 2 * (Split.N a.parent) (a.suffixChain.sample k) ^ (ε + u) ≤ H)
    (σ : Fin ((Split.W a.parent) (a.suffixChain.sample k)) → Measure Incidence)
    (hσ : ∀ g, σ g ≤ Split.mu a.parent (a.suffixChain.sample k) g)
    (hcover : ∀ j g, σ g {z | ∃ i, (P j).γ i = g ∧ z ∈ (P j).C i}ᶜ = 0)
    (hbad : ∀ j g, σ g (WidthGeometry.narrowEvent (Layer.ofChart (P j)) ε u g) = 0)
    (hmass : ENNReal.ofReal ((Split.N a.parent) (a.suffixChain.sample k) ^ (-v)) ≤
      ∑ g, ENNReal.ofReal ((Split.ω a.parent) (a.suffixChain.sample k) g) * σ g univ)
    (hprofile : ∀ j, (Split.N a.parent) (a.suffixChain.sample k) ^
      |(Split.f a.parent) (a.depth j) - d * a.depth j| ≤ B)
    (hguard : ∀ r h, 0 ≤ r → r < (Split.L a.parent) → h ≤ κ * r - gain →
      ¬Split.Chart a.parent G r (Split.L a.parent) h loss false (a.suffixChain.sample k))
    (htime : ∀ j, a.time j + ε ≤ κ * a.depth j + β)
    (hβ : (Split.N a.parent) (a.suffixChain.sample k) ^ β ≤ B)
    (hgain : (Split.N a.parent) (a.suffixChain.sample k) ^ gain ≤ B)
    (hτ : (Split.N a.parent) (a.suffixChain.sample k) ^ τ ≤ B)
    (hpure : ∀ j g, σ g (pureException a.parent (a.suffixChain.sample k) g (a.depth j) τ) = 0) :
    ∃ layers : Fin a.count → Layer ((Split.W a.parent) (a.suffixChain.sample k)),
      ∀ j, a.OriginalLayerGood k M ε v H B d κ σ j (layers j) := by
  classical
  have hN : 1 ≤ (Split.N a.parent) (a.suffixChain.sample k) := exact_N_ge_one a.parent_exact _
  have hsingle (j : Fin a.count) : ∃ F,
      a.OriginalLayerGood k M ε v H B d κ σ j F := by
    obtain ⟨F, hT, hcd, hwide, hcoverF⟩ := exists_wide_true_layer (P j) hN hM hεv hH
      σ hσ (hcover j) (hbad j) hmass
    have hbQ := layer_block_bounds (F := Layer.ofChart (P j)) hN (P j).hcd (hM.trans hMG) hεloss
      (hguard (a.depth j) · (a.depth_bounds j).1 (a.depth_bounds j).2)
      (htime j) hβ hgain
    have hb : (Split.N a.parent) (a.suffixChain.sample k) ^ (κ * a.depth j) / B ≤
        (2 : ℝ) ^ F.T ∧ (2 : ℝ) ^ F.T ≤
          B * (Split.N a.parent) (a.suffixChain.sample k) ^ (κ * a.depth j) := by
      change (Split.N a.parent) (a.suffixChain.sample k) ^ (κ * a.depth j) / B ≤
        (2 : ℝ) ^ (P j).T ∧ (2 : ℝ) ^ (P j).T ≤
          B * (Split.N a.parent) (a.suffixChain.sample k) ^ (κ * a.depth j) at hbQ
      simpa only [hT] using hbQ
    refine ⟨F, hcd, hwide, hcoverF, hprofile j, hb.1, hb.2, ?_⟩
    intro g
    exact pureObservation_cap a.parent_exact _ g (a.depth_bounds j).1 (a.depth_bounds j).2.le
      (hσ g) (hpure j g) hτ
  choose layers hlayers using hsingle
  exact ⟨layers, hlayers⟩

end PathGeometry.OriginalView

end

end Submission.Obl.k4_scalar_guarded_entropic_path
