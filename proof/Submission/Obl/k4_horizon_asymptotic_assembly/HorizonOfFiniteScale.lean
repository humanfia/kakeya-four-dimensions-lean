/- Adapted from this LOT tree, obligation o103, session x0354, commit162b3a6,
Submission/Obl/k4_initial_horizon_bound/HorizonOfFiniteScale.lean.
Named forms and Boolean calculus originally came from o103/x0360, commits642b39c andb0c6023;
the finite interface definitions came from o160/x0559/b0539eb, as attributed below. -/

import Submission.Obl.k4_horizon_asymptotic_assembly.FiniteScaleToHorizon
import Submission.Obl.k4_horizon_light_cell_mass

/-! Use the accepted light-cell theorem in the finite-to-asymptotic conversion. -/

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_horizon_asymptotic_assembly.Outer

set_option maxHeartbeats 1600000 in
theorem horizon_of_finite_scale_atlas (hf : FiniteScaleAtlas) : HorizonStatement := by
  intro N K L d S η W ω ν E P B f g G hp
  apply initial_horizon_from_finite_scale hf hp
  obtain ⟨H₀, hH₀⟩ := Submission.k4_horizon_light_cell_mass N K L d S η W ω ν E P B f g G hp
  refine ⟨H₀, ?_⟩
  intro τ hτ
  obtain ⟨c, hc, he⟩ := hH₀ τ hτ
  refine ⟨c, hc, he.mono ?_⟩
  intro k hk ρ hρ hρH
  have hh := hk ρ ρ hρ hρH hρ hρH
  have hpow : N k ^ (-f L - τ) * ρ * ρ ^ 2 = N k ^ (-f L - τ) * ρ ^ 3 := by ring
  simpa only [finiteScaleLightMass, xl, obsl, dl, hpow] using hh

end Submission.Obl.k4_horizon_asymptotic_assembly.Outer
