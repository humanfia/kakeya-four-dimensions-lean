import Submission.Obl.k4_general_parent_projected_layers.Support.WorldObservation
import Submission.Obl.k4_general_parent_projected_layers.Support.ScalarCropLaw
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery (scalarCell scalarX)
open Submission.Obl.k4_horizontal_supercritical_three_projections (chartLaw_supported chartLaw)

noncomputable section

/-- Original terminal tables transfer to each conditional current law using
its exact native scalar observations. -/
theorem world_scalar_terminal_support {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (K chi g sigma a : ℝ) (C : Set α) (hC : MeasurableSet C) (u : Fin 4 → ℤ)
    (E : Set (α × ℝ)) (hE : ∀ᵐ z ∂ζ, z ∈ E)
    (F : Finset ((Fin 2 → ℤ) × ℤ))
    (hF : ∀ z ∈ E, projectedWorldTag chi g (b z.1) = u →
      (projectedCell sigma g (projectedWorldRepresentatives K chi g u 2)
        (projectedWorldRepresentatives K chi g u 3) (b z.1) z.2,
          ⌊eval (trajectory (b z.1) z.2) P / a⌋) ∈ F) :
    ∀ᵐ z ∂scalarCropLaw ν ζ (projectedWorldCrop C b chi g u),
      (scalarCell (worldScalarCoefficients P b K chi g C u z.1) z.2 sigma,
        ⌊scalarX (worldScalarCoefficients P b K chi g C u z.1) z.2 / a⌋) ∈ F := by
  have hcrop := measurableSet_projectedWorldCrop hC b hb chi g u
  have hsource := chartLaw_supported ν ζ hcrop
  have hE' : ∀ᵐ z ∂scalarCropLaw ν ζ (projectedWorldCrop C b chi g u), z ∈ E :=
    Measure.ae_smul_measure (ae_restrict_of_ae hE) _
  filter_upwards [hsource, hE'] with z hz hzE
  have hy := nativeScalarCoefficients_y P b g
    (projectedWorldRepresentatives K chi g u 2)
    (projectedWorldRepresentatives K chi g u 3) hz z.2
  have hx := nativeScalarCoefficients_x P hP b g
    (projectedWorldRepresentatives K chi g u 2)
    (projectedWorldRepresentatives K chi g u 3) hz z.2
  have ht := hF z hzE hz.2
  change ((![⌊z.2 / sigma⌋,
    ⌊Submission.Obl.k4_uncapped_native_capping.scalarY
      (nativeScalarCoefficients P b g _ _ _ z.1) z.2 / sigma⌋] : Fin 2 → ℤ),
    ⌊Submission.Obl.k4_uncapped_native_capping.scalarX
      (nativeScalarCoefficients P b g _ _ _ z.1) z.2 / a⌋) ∈ F
  rw [hy, hx]
  exact ht

end

end Submission.Obl.k4_general_parent_projected_layers
