-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceTrackingSpec
import Submission.Obl.k4_finite_affine_parent_sources.SourceComponents

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- The tracking component in the combined source-preparation interface. -/
theorem sourceTrackingSpec : SourceTrackingSpec := by
  intro d₁ κ₁ ℓ S η ρ hd₁ hd₁' hκ₁ hκ₁' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨u₀, hu₀, hU⟩ := sourceTrackingFullAxesSpec
    d₁ κ₁ ℓ S η ρ hd₁ hd₁' hκ₁ hκ₁' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨u₀, hu₀, fun u hu hu' => ?_⟩
  obtain ⟨g₀, hg₀, hG⟩ := hU u hu hu'
  refine ⟨g₀, hg₀, fun gain hg hg' m sg δ₀ hgrid hδ hδgain => ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨Mprep, hP⟩ := hG gain hg hg' m sg δ₀ hgrid hδ hδgain
    N K L d W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨Mprep, fun ε hε => ?_⟩
  obtain ⟨σp, hσp, kp, hPk⟩ := hP ε hε
  refine ⟨σp, hσp, kp, fun σ hσ hσ' k hk p hp Hres hHm hmass => ?_⟩
  rcases hPk σ hσ hσ' k hk p hp Hres hHm hmass with hc | ht
  · exact Or.inl hc
  right
  intro a τ D hDa hbandlo hbandhi hroom hτ hτε hτu hτhalf hDS hDm hDne hD₀ hDK hDd
    hDopen hDend hparentAxis hlabelAxes hpf hlf
  have haxes : D.FullAxes n (N k ^ (-(u * L * trackingSlackExponent n ℓ ρ / 2))) := by
    refine ⟨?_, ?_⟩
    · simpa only [sourceAxisMask, trackingSlackExponent, hDa] using hparentAxis
    · simpa only [sourceAxisMask, trackingSlackExponent] using hlabelAxes
  exact ht a τ D hDa hbandlo hbandhi hroom hτ hτε hτu hτhalf hDS hDm hDne hD₀ hDK hDd
    haxes hDopen hDend hpf hlf

/-- Only the probability selection component remains once tracking has
been supplied by the original path geometry. -/
theorem sourcePreparation_of_selection (h : SourceSelectionSpec) : SourcePreparation :=
  sourcePreparation_of_components h sourceTrackingSpec

end

end Submission.Obl.k4_finite_affine_parent_sources
