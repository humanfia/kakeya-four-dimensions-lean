-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/DensityCutoff.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/DensityCutoff.lean (namespace renamed).

import Mathlib

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set

/-- Truncating at an observation-density ceiling gives a domination bound for every
further measurable incidence selection, under its original measure. -/
theorem map_restrict_density_cutoff_le {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) (ρ : Measure X) (obs : Ω → X) (hobs : Measurable obs)
    (g : X → ENNReal) (hg : Measurable g) (hlaw : ν.map obs = ρ.withDensity g)
    (H : ENNReal) (E : Set Ω) (hsub : E ⊆ {p | g (obs p) ≤ H}) :
    (ν.restrict E).map obs ≤ H • ρ := by
  let G : Set X := {x | g x ≤ H}
  have hG : MeasurableSet G := measurableSet_le hg measurable_const
  apply Measure.le_iff.mpr
  intro A hA
  have hAG := hA.inter hG
  rw [Measure.map_apply hobs hA, Measure.restrict_apply (hA.preimage hobs)]
  calc
    _ ≤ ν (obs ⁻¹' (A ∩ G)) := measure_mono (by
      rintro p ⟨hpA, hpE⟩
      exact ⟨hpA, hsub hpE⟩)
    _ = (ν.map obs) (A ∩ G) := (Measure.map_apply hobs hAG).symm
    _ = ∫⁻ x in A ∩ G, g x ∂ρ := by rw [hlaw, withDensity_apply _ hAG]
    _ ≤ ∫⁻ x in A ∩ G, H ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hAG] with x hx
      exact hx.2
    _ = H * ρ (A ∩ G) := setLIntegral_const _ _
    _ ≤ H * ρ A := by gcongr; exact inter_subset_left
    _ = (H • ρ) A := by rw [Measure.smul_apply, smul_eq_mul]

/-- A dominated observation law retains the support of its selected incidences. -/
theorem map_restrict_compl_eq_zero {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure Ω) (obs : Ω → X) (hobs : Measurable obs)
    (E : Set Ω) (S : Set X) (hS : MeasurableSet S)
    (hsupport : ∀ p ∈ E, obs p ∈ S) :
    ((ν.restrict E).map obs) Sᶜ = 0 := by
  rw [Measure.map_apply hobs hS.compl,
    Measure.restrict_apply (hS.compl.preimage hobs)]
  have he : (obs ⁻¹' Sᶜ) ∩ E = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, hpE⟩
    exact hp (hsupport p hpE)
  rw [he, measure_empty]

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
