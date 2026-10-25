import Submission.Obl.k4_scalar_guarded_tangent_preparation.Construction

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open Submission.Obl.k4_scalar_linear_critical_extremizers

/-- The three constructions use the same exact parents and original
weights. The half-mass law preparation preserves the reserve needed by
simultaneous layer completion. -/
theorem assemble
    (hI : Split.Initial) (hC : Split.Calculus)
    (hpath : EntropicPathConstruction)
    (hcaps : ReferenceCapPreparation)
    (hfinish : FullPriorLayerCompletion) :
    Split.Critical → GuardedPrepared := by
  intro hcritical
  obtain ⟨p, sample, scale, H, buffer, B, M, count, node, depth, time,
    layers, σ, d, κ, S, hgeometry, hlaws⟩ := hpath hI hC hcritical
  obtain ⟨K, ρ, π, hρ, hmass, hcap⟩ := hcaps
    (fun k => (p k).N (sample k) ^ scale k) B d S
    (fun k => (p k).W (sample k)) (fun k => (p k).weight (sample k)) σ hlaws
  have hreserve : ∀ k, ENNReal.ofReal (2 * (H k)⁻¹) ≤
      ENNReal.ofReal (1 / 2 : ℝ) *
        ∑ g, ENNReal.ofReal ((p k).weight (sample k) g) * σ k g Set.univ := by
    rcases hgeometry with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _⟩
    exact h
  exact hfinish p sample scale H buffer B M count node depth time layers σ d κ S
    hgeometry K ρ π hρ (fun k => (hreserve k).trans (hmass k)) hcap

end Submission.Obl.k4_scalar_guarded_tangent_preparation
