-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.FiniteVectorVelocityCodes
import Submission.Obl.k4_finite_affine_parent_sources.VelocityCodeReadout

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

/-- The finite original planar-bin alphabet, before choosing a parent
axis. Empty and repeated history codes are not additional palette atoms. -/
abbrev PlanarPaletteCodes (R fine : ℝ) :=
  Fin 2 → {j : ℤ // j ∈ Finset.Icc ⌊-R / fine⌋ ⌊R / fine⌋}

theorem exists_planar_palette_code {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (velocity : Ω → Fin 2 → ℝ) (hvel : Measurable velocity)
    {R fine : ℝ} (hR : 0 ≤ R) (hfine : 0 < fine)
    (hbound : ∀ᵐ z ∂μ, ∀ e, |velocity z e| ≤ R) :
    ∃ U : Ω → PlanarPaletteCodes R fine, Measurable U ∧
      ∀ᵐ z ∂μ, ∀ e, (U z e : ℤ) = ⌊velocity z e / fine⌋ := by
  obtain ⟨n, -, code, _, palette, hcode, hdecode, -, -⟩ :=
    exists_history_vector_velocity_code 2 μ (fun _ => ()) measurable_const
      velocity hvel fine R hfine hR hbound
  refine ⟨fun z => palette (code z), (measurable_of_finite palette).comp hcode, ?_⟩
  filter_upwards [hdecode] with z hz
  exact hz.2

/-- A finite palette atom is exactly its original planar velocity cell
almost everywhere; histories have been forgotten without splitting atoms. -/
theorem planar_palette_fiber_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (velocity : Ω → Fin 2 → ℝ) {R fine : ℝ}
    (U : Ω → PlanarPaletteCodes R fine)
    (hcode : ∀ᵐ z ∂μ, ∀ e, (U z e : ℤ) = ⌊velocity z e / fine⌋)
    (c : PlanarPaletteCodes R fine) :
    ∀ᵐ z ∂μ, U z = c ↔
      (fun e => ⌊velocity z e / fine⌋) = (fun e => (c e : ℤ)) := by
  filter_upwards [hcode] with z hz
  constructor
  · intro h
    funext e
    exact (hz e).symm.trans (congrArg (fun u => (u e : ℤ)) h)
  · intro h
    funext e
    apply Subtype.ext
    exact (hz e).trans (congrFun h e)

theorem PFrame.planar_palette_center_close {Ω : Type*} [MeasurableSpace Ω]
    (Φ : PFrame) (μ : Measure Ω) (line : Ω → ℕ × (Fin 6 → ℝ))
    (velocity : Ω → Fin 2 → ℝ) (hvel : ∀ z e, velocity z e = Submission.Lib.K4XInterface.gv (line z) e)
    {R fine H : ℝ} (hfine : 0 < fine)
    (hrow : |Φ.F.q| * (|Φ.F.D⁻¹ 0 0| + |Φ.F.D⁻¹ 0 1|) ≤ H)
    (U : Ω → PlanarPaletteCodes R fine)
    (hcode : ∀ᵐ z ∂μ, ∀ e, (U z e : ℤ) = ⌊velocity z e / fine⌋) :
    ∀ᵐ z ∂μ, |Φ.eb (line z) 3 -
      Φ.majorVelocityCenter fine (fun e => (U z e : ℤ))| ≤ H * fine := by
  filter_upwards [hcode] with z hz
  apply Φ.majorVelocityCenter_close hfine hrow (line z)
  intro e
  rw [hz e, hvel z e]

end
end Submission.Obl.k4_finite_affine_parent_sources
