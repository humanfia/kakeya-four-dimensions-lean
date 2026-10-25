import Submission.Obl.k4_finite_affine_parent_sources.FlatCut
import Submission.Obl.k4_finite_affine_parent_sources.SourceTrackingComponent
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSchedule

/-!
# From `SourcePreparation` to the frozen statement of o279

`FlatSourcePreparation` (o232's `FlatCut`, x0859) is the frozen type of o279 with its
lambda-bound names replaced by their definitions; o232's glue applies its converse
`sourcePreparation_of_flat` to the frozen stub with `exact`. `flat_of_sourcePreparation`
repacks the structured `SourcePreparation` back into the flat fields, without changing any
law or path field.

With the tracking component supplied by the geometric preparation
(`sourcePreparation_of_selection`), the frozen statement follows from the selection
component alone (`flat_of_selection`, `flat_of_selectionLate`).

Written by x0994 for o279.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- Repack the structured source alternative into the explicit fields of the frozen type. -/
theorem flat_of_sourcePreparation (h : SourcePreparation) : FlatSourcePreparation := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨m, s, gain, δ₀, unit, hg, hgain, hgain', hδ, hδ', h⟩ :=
    h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨m, s, gain, δ₀, unit, hg, hgain, hgain', hδ, hδ', ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨M, h⟩ := h N K L d W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨M, fun ε hε => ?_⟩
  obtain ⟨σ, hσ, k₀, h⟩ := h ε hε
  refine ⟨σ, hσ, k₀, ?_⟩
  intro k hk r T nw κ C lev par γ j c u Q R A F lst hp H hH hmass
  let p : PathData (W k) := ⟨r, T, nw, κ, C, lev, par, γ, j, c, u, Q, R, A, F, lst⟩
  rcases h k hk p hp H hH hmass with hfound | ⟨st, hgood, hsrc⟩
  · exact Or.inl hfound
  · exact Or.inr ⟨st.N, st.K, st.ν, st.μ, st.ρ, st.π, st.b, st.P, st.T, st.nl, st.j, st.A,
      st.B, st.c, st.F, hgood, hsrc⟩

/-- The frozen statement from the selection component. -/
theorem flat_of_selection (h : SourceSelectionSpec) : FlatSourcePreparation :=
  flat_of_sourcePreparation (sourcePreparation_of_selection h)

/-- The frozen statement from the selection component in its lateness form. -/
theorem flat_of_selectionLate (h : SourceSelectionLateSpec) : FlatSourcePreparation :=
  flat_of_selection (sourceSelectionSpec_of_late h)

end

end Submission.Obl.k4_finite_affine_parent_sources
