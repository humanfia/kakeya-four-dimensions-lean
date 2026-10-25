import Mathlib

/-!
# Frozen observation spaces

The frozen joint observation of o125 lands in `((Fin 2 → ℝ) × ℤ) × ℤ` with reference
`(volume ⊗ count) ⊗ count`, while the finite band estimates are proved on
`(Fin 2 → ℝ) × (ℤ × ℤ)` with reference `volume ⊗ count`. Reassociation is measure
preserving between them, so exact densities, density versions, bad-mass estimates and
absolute continuity transfer. All code was written in this workspace by x0424.
-/

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set
open scoped ENNReal

/-- Counting measure on `ℤ × ℤ` is the product of the counting measures. -/
theorem count_prod_count_int :
    (Measure.count : Measure ℤ).prod (Measure.count : Measure ℤ) =
      (Measure.count : Measure (ℤ × ℤ)) := by
  apply Measure.ext_of_singleton
  intro a
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp

/-- Reassociation carries the frozen joint reference to the canonical reference. -/
theorem measurePreserving_jointAssoc :
    MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((Fin 2 → ℝ) × ℤ) × ℤ ≃ᵐ (Fin 2 → ℝ) × (ℤ × ℤ))
      (((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure ℤ)).prod
        (Measure.count : Measure ℤ))
      ((volume : Measure (Fin 2 → ℝ)).prod (Measure.count : Measure (ℤ × ℤ))) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by rw [Measure.prodAssoc_prod, count_prod_count_int]

/-- A density pushed through a measure-preserving equivalence. -/
theorem map_withDensity_of_measurePreserving {Y₁ Y₂ : Type*}
    [MeasurableSpace Y₁] [MeasurableSpace Y₂] {ρ₁ : Measure Y₁} {ρ₂ : Measure Y₂}
    (e : Y₁ ≃ᵐ Y₂) (he : MeasurePreserving e ρ₁ ρ₂) (G : Y₁ → ℝ≥0∞) :
    (ρ₁.withDensity G).map e = ρ₂.withDensity (G ∘ e.symm) := by
  ext A hA
  rw [Measure.map_apply e.measurable hA, withDensity_apply _ (e.measurable hA),
    withDensity_apply _ hA, ← he.map_eq, MeasurableEquiv.restrict_map, lintegral_map_equiv]
  simp

/-- Exact densities transfer along a measure-preserving reparametrization of the target. -/
theorem density_transfer {Ω Y₁ Y₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y₁] [MeasurableSpace Y₂] {ρ₁ : Measure Y₁} {ρ₂ : Measure Y₂}
    (e : Y₁ ≃ᵐ Y₂) (he : MeasurePreserving e ρ₁ ρ₂)
    (μ : Measure Ω) (Q : Ω → Y₁) (hQ : Measurable Q) (G : Y₁ → ℝ≥0∞)
    (h : μ.map Q = ρ₁.withDensity G) :
    μ.map (fun p => e (Q p)) = ρ₂.withDensity (G ∘ e.symm) := by
  have hcomp : (fun p => e (Q p)) = e ∘ Q := rfl
  rw [hcomp, ← Measure.map_map e.measurable hQ, h, map_withDensity_of_measurePreserving e he]

/-- Conversely, a density for the reparametrized observation gives one for the original. -/
theorem density_transfer_symm {Ω Y₁ Y₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y₁] [MeasurableSpace Y₂] {ρ₁ : Measure Y₁} {ρ₂ : Measure Y₂}
    (e : Y₁ ≃ᵐ Y₂) (he : MeasurePreserving e ρ₁ ρ₂)
    (μ : Measure Ω) (Q : Ω → Y₁) (hQ : Measurable Q) (g : Y₂ → ℝ≥0∞)
    (h : μ.map (fun p => e (Q p)) = ρ₂.withDensity g) :
    μ.map Q = ρ₁.withDensity (g ∘ e) := by
  have hQ' : Measurable (fun p => e (Q p)) := e.measurable.comp hQ
  have hback := density_transfer e.symm he.symm μ (fun p => e (Q p)) hQ' g h
  simpa only [MeasurableEquiv.symm_apply_apply, MeasurableEquiv.symm_symm] using hback

/-- A bad-mass estimate valid for every density version of the reparametrized observation
holds for every density version of the original observation. -/
theorem bad_mass_transfer {Ω Y₁ Y₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y₁] [MeasurableSpace Y₂] {ρ₁ : Measure Y₁} {ρ₂ : Measure Y₂}
    (e : Y₁ ≃ᵐ Y₂) (he : MeasurePreserving e ρ₁ ρ₂)
    (μ : Measure Ω) (Q : Ω → Y₁) (hQ : Measurable Q) (P : ℝ≥0∞ → Prop) (B : ℝ≥0∞)
    (hband : ∀ g : Y₂ → ℝ≥0∞, Measurable g →
      μ.map (fun p => e (Q p)) = ρ₂.withDensity g → μ {p | P (g (e (Q p)))} ≤ B) :
    ∀ G : Y₁ → ℝ≥0∞, Measurable G → μ.map Q = ρ₁.withDensity G →
      μ {p | P (G (Q p))} ≤ B := by
  intro G hG hlaw
  have h := hband (G ∘ e.symm) (hG.comp e.symm.measurable)
    (density_transfer e he μ Q hQ G hlaw)
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using h

/-- An exact density makes the Radon-Nikodym derivative an exact density as well. -/
theorem rnDeriv_density_of_density {Y : Type*} [MeasurableSpace Y]
    (ν ρ : Measure Y) [SigmaFinite ρ] (f : Y → ℝ≥0∞) (hf : Measurable f)
    (h : ν = ρ.withDensity f) :
    Measurable (ν.rnDeriv ρ) ∧ ν = ρ.withDensity (ν.rnDeriv ρ) := by
  refine ⟨Measure.measurable_rnDeriv ν ρ, ?_⟩
  have hae : ν.rnDeriv ρ =ᵐ[ρ] f := by
    rw [h]
    exact Measure.rnDeriv_withDensity ρ hf
  rw [withDensity_congr_ae hae]
  exact h

end Submission.Obl.k4_marked_scalar_grid_selection
