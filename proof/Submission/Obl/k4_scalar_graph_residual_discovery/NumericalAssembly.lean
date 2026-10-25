import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryScaleExistence
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryBudgetStatement

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- The remaining power-counting calculation. All physical mesh and
block-scale comparisons are supplied by `exists_discovery_scale_parameters`. -/
def DiscoveryPowerExistenceStatement : Prop :=
  ∀ N H Hg K : ℕ → ℝ,
    (∀ k, 1 ≤ N k) → Tendsto N atTop atTop →
    Subpower N H → Subpower N Hg → Subpower N K →
    ∀ d S Cmk : ℝ, d ≤ 1 → 0 < S → 0 < Cmk →
    ∀ C₁ C : ℕ, ∀ α δ : ℝ, 0 < α → 0 < δ →
      ∃ J₁ J₂ : ℕ, 1 ≤ J₁ ∧ 1 ≤ J₂ ∧ 2 / (J₁ : ℝ) < 1 ∧
        ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ k in atTop,
          Nonempty (DiscoveryPowerBounds (N k) (H k) (Hg k) (K k) d S δ α Cmk τ C₁ C J₁ J₂)

/-- The complete numerical discovery budget follows from its power
calculation and the checked independent scale calculation. -/
theorem discovery_budgets_of_power_existence
    (hpower : DiscoveryPowerExistenceStatement) : DiscoveryBudgetExistenceStatement := by
  intro N K H m h hN hNt hK hH hm d κ S hd hd₁ hκ hS hh hscale M hM cζ hcζ L hL Cmk hCmk
  have hN₁ (k : ℕ) : 1 ≤ N k := by linarith [hN k]
  obtain ⟨C, C₁, hC, hC₁, L', hLL', hL', hC₁L, hscales⟩ :=
    exists_discovery_scale_parameters M hM hκ hcζ hL
  refine ⟨C, C₁, hC, hC₁, L', hLL', hL', hC₁L, ?_⟩
  intro Hg hHg B hB α hα δ hδ
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJsmall, τ, hτ, hpowers⟩ :=
    hpower N H Hg K hN₁ hNt hH hHg hK d S Cmk hd₁ hS hCmk C₁ C α δ hα hδ
  obtain ⟨T, hT, hscaleBounds⟩ := hscales N H Hg K h m hN₁ hNt hH hHg hK
    (fun k => (hm k).1) hh (hscale.mono (fun _ hk => hk.1)) B hB J₁ hJsmall τ hτ
  refine ⟨J₁, J₂, hJ₁, hJ₂, T, hT, ?_⟩
  filter_upwards [hpowers, hscaleBounds] with k hp hs
  obtain ⟨p⟩ := hp
  obtain ⟨s⟩ := hs
  exact ⟨p.toBudget s⟩

end Submission.Obl.k4_scalar_graph_residual_discovery
