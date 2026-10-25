/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/ProfileBridge.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.Interface
import Submission.Obl.k4_native_grid_profile_extension.NativeRefinement
import Submission.Obl.k4_native_grid_profile_extension.Profiles.DensityRefinement
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileGrid

/-!
# Canonical densities for profile compactness
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set Filter MeasureTheory
open scoped Topology ENNReal

local instance : SigmaFinite nativeReference := by
  unfold nativeReference
  infer_instance

/-- The native helper map is the expanded observation in the split interface. -/
theorem nativeObservation_eq_Observation (N r u : ℝ) :
    nativeObservation N r u = Observation N r u := by
  funext p
  simp [nativeObservation, angularObservation, pureObservation, baseObservation,
    trajectoryPoint, planarVelocity, Observation, dyadicWidth]

noncomputable def nativeDensity (μ : Measure (Coefficients × ℝ)) (N r u : ℝ) :
    AngularObservationSpace → ℝ≥0∞ :=
  (μ.map (nativeObservation N r u)).rnDeriv nativeReference

theorem measurable_nativeDensity (μ : Measure (Coefficients × ℝ)) (N r u : ℝ) :
    Measurable (nativeDensity μ N r u) := Measure.measurable_rnDeriv _ _

/-- Existence of any density makes the canonical Radon--Nikodym representative exact. -/
theorem nativeDensity_law (μ : Measure (Coefficients × ℝ)) [IsFiniteMeasure μ]
    (N r u : ℝ)
    (hExists : ∃ G : AngularObservationSpace → ℝ≥0∞, Measurable G ∧
      μ.map (Observation N r u) = Reference.withDensity G) :
    μ.map (nativeObservation N r u) = nativeReference.withDensity (nativeDensity μ N r u) := by
  obtain ⟨G, hG, hmap⟩ := hExists
  have hac : μ.map (nativeObservation N r u) ≪ nativeReference := by
    rw [nativeObservation_eq_Observation, hmap]
    exact withDensity_absolutelyContinuous _ _
  exact (Measure.withDensity_rnDeriv_eq _ _ hac).symm

/-- Density typicality is a property of the law, so a chosen representative suffices. -/
theorem typical_of_nativeDensity {N : ℕ → ℝ}
    {μ : ℕ → Measure (Coefficients × ℝ)} [∀ k, IsFiniteMeasure (μ k)]
    {R U : ℝ} {F : ℝ → ℝ → ℝ} (hExists : DensityExists N μ R U)
    (htypical : ∀ r ∈ Icc (0 : ℝ) R, ∀ u ∈ Icc (0 : ℝ) U,
      Profiles.HasTypicalDensity N μ
        (fun k p => nativeDensity (μ k) (N k) r u (nativeObservation (N k) r u p))
        (F r u)) : Typical N μ R U F := by
  intro r u τ hr hrR hu huU hτ
  obtain ⟨c, hc, hbound⟩ := htypical r ⟨hr, hrR⟩ u ⟨hu, huU⟩ τ hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound] with k hk
  intro G hG hGmap
  have hcanon := nativeDensity_law (μ k) (N k) r u (hExists k r u hr hrR hu huU)
  have hGmap' : (μ k).map (nativeObservation (N k) r u) = nativeReference.withDensity G := by
    simpa only [nativeObservation_eq_Observation, nativeReference] using hGmap
  have heq := observation_density_bad_mass_eq (μ k) nativeReference
    (nativeObservation (N k) r u) (measurable_nativeObservation _ _ _)
    G (nativeDensity (μ k) (N k) r u) hG (measurable_nativeDensity _ _ _ _)
    hGmap' hcanon (ENNReal.ofReal (N k ^ (-F r u - τ)))
    (ENNReal.ofReal (N k ^ (-F r u + τ)))
  simpa only [nativeObservation_eq_Observation] using heq.trans_le hk

end Submission.Obl.k4_native_grid_profile_extension
