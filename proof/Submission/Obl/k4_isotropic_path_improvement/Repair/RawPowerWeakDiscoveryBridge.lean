-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawPowerWeakDiscoveryBridge.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.Expanded
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.DenseJet.Bridge
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakInterface
import Submission.Obl.k4_isotropic_path_improvement.Repair.SubpowerWeakDiscoveryRepair
import Submission.Obl.k4_seven_direction_local_degree_restoration

/-!
Adapted from this LOT tree o143/x0542, commit f027eb90, main theorem body.
The geometric hypothesis is the power-mass variant of o204/x0733 ba2d6042.
Local restoration and sheet Remez are imported accepted results. This bridge
preserves the weak narrow-atlas alternative and does not assume strong discovery.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakDiscoveryBridge

open MeasureTheory SubpowerWeakDiscoveryRepair RawRestoration

/-- Algebraic restoration converts the raw weak engine into the post-restoration
weak engine, preserving the original laws, requested formats, and both slacks. -/
theorem weak_uniform_of_raw (hRaw : RawPowerWeakInterface.WeakAssertion) :
    WeakUniformDiscovery := by
  intro hmk d₁ κ₁ S η ρ hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ
  have hlr : LocalRestorationAssertion :=
    Submission.k4_seven_direction_local_degree_restoration
  obtain ⟨Cloc, hCloc, hrestore⟩ := apply_local_restoration hlr
  obtain ⟨D, hD⟩ := hRaw hmk Cloc hCloc d₁ κ₁ S η ρ
    hd₁ hd₁1 hκ₁ hκ₁1 hS hη hρ hdρ (1 / 8) (by norm_num)
  obtain ⟨J, hJ, hjet⟩ := denseJetAssertion D
  obtain ⟨m, s, gain, δ₀, u₀, hgrid, _, hdiscovery⟩ := hD J hJ hjet
  rcases hgrid with ⟨⟨hm, _, _, _⟩, hgain, hgain8, hδ₀, hδgain,
    _, _, hs, _, _, _, _, hu₀, _⟩
  have hsgrid : s = WeakUniformDiscoveryRepair.uniformGrid m := by
    funext i
    exact hs i
  subst s
  refine ⟨m, gain, δ₀, u₀, hm, hgain, hgain8, hδ₀, hδgain, hu₀, ?_⟩
  intro N K L d W ω ν E P B f g G hproblem hprofile Mp Dp
  obtain ⟨Mi, Di, hstage⟩ := hdiscovery N K L d W ω ν E P B f g G
    hproblem hprofile Mp Dp
  refine ⟨Mi, Di, ?_⟩
  intro τ hτ α hα hα1
  obtain ⟨σ, hσ, k₀, hlate⟩ := hstage Mi Di le_rfl le_rfl τ hτ α hα hα1
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass
  rcases hlate k hk r T nw κ C lev par γ j c u Q R A F lst hpath H hH hmass with
    (hwidth | hdirect | hsampled) | hnarrow
  · exact Or.inl hwidth
  · exact Or.inr (Or.inl hdirect)
  · apply Or.inr
    apply Or.inl
    have hsamp := rawSampledCandidate_implies_sampled
      (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H hsampled
    have hnorm := sampledCandidate_implies_normalized hjet
      (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H hsamp
    exact normalizedCandidate_implies_candidate Cloc hrestore
      (N k) L (W k) (ν k) (B k) Mi d₁ ρ gain τ r T C lev γ j A H
      (hproblem.1 k) hnorm
  · apply Or.inr
    apply Or.inr
    obtain ⟨i, β, hi, _, hsi, hβ, _, ha⟩ := hnarrow
    refine ⟨i, β, (fun w jt At Ft known => known ∧ ∃ b : Fin C,
      lev b = i ∧ γ b = w ∧ j b = (jt : ℕ) ∧ At ⊆ A b ∧ Ft ⊆ F b),
      hi, hsi, hβ, ?_, ha⟩
    intro w jt At Ft known h
    exact h.1

theorem repaired_of_raw (hRaw : RawPowerWeakInterface.WeakAssertion) : O106Repair.frozen116 :=
  frozen_repaired_discovery_of_weak (weak_uniform_of_raw hRaw)

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawPowerWeakDiscoveryBridge
