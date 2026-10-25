/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/ScalarCropLaw.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.ZoomLaw
import Submission.Obl.k4_horizontal_supercritical_three_projections.Conditioning
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! Original-prior conditioning for one scalar projected group. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

abbrev scalarCropLaw (ν : Measure α) (μ : Measure (α × ℝ)) (C : Set α) : Measure (α × ℝ) :=
  Submission.Obl.k4_horizontal_supercritical_three_projections.chartLaw ν μ C

theorem scalarCropLaw_eq_zoomLaw (ν : Measure α) (μ : Measure (α × ℝ)) (C : Set α) :
    scalarCropLaw ν μ C = zoomLaw μ (C ×ˢ univ) 0 1 (ν C) := by
  have htime : zoomTime (α := α) 0 1 = id := by
    funext p
    simp only [zoomTime, sub_zero, div_one, Prod.eta, id_eq]
  rw [zoomLaw, htime, Measure.map_id]
  rfl

theorem scalarCropLaw_domination {ν : Measure α} [SFinite ν] {μ : Measure (α × ℝ)}
    {K : ℝ≥0∞} (hμ : μ ≤ K • ν.prod volume) {C : Set α} (hC : MeasurableSet C) :
    scalarCropLaw ν μ C ≤ K • (condPrior ν C).prod volume := by
  exact Submission.Obl.k4_horizontal_supercritical_three_projections.chartLaw_domination ν μ C K hμ

theorem scalarCropLaw_apply (ν : Measure α) (μ : Measure (α × ℝ)) (C : Set α)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    scalarCropLaw ν μ C E = (ν C)⁻¹ * μ (E ∩ C ×ˢ univ) :=
  Submission.Obl.k4_horizontal_supercritical_three_projections.chartLaw_apply ν μ C hE

theorem scalarCropLaw_restore (ν : Measure α) (μ : Measure (α × ℝ)) (C : Set α)
    (h0 : ν C ≠ 0) (htop : ν C ≠ ⊤) {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hEC : E ⊆ C ×ˢ univ) :
    ν C * scalarCropLaw ν μ C E = μ E := by
  rw [scalarCropLaw_apply ν μ C hE, inter_eq_left.mpr hEC,
    ← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]

theorem scalarCropLaw_unit_support (ν : Measure α) (μ : Measure (α × ℝ)) (C : Set α)
    (hunit : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) :
    scalarCropLaw ν μ C (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
  Submission.Obl.k4_horizontal_supercritical_three_projections.chartLaw_time_support ν μ C hunit

theorem scalarCropLaw_event_le {ν : Measure α} {μ ρ : Measure (α × ℝ)}
    (hρ : ρ ≤ μ) {C : Set α} (hC : MeasurableSet C)
    (hunit : ∀ᵐ z ∂μ, z.2 ∈ Icc (0 : ℝ) 1) {E F : Set (α × ℝ)}
    (hsub : ∀ z, z.1 ∈ C → z.2 ∈ Icc (0 : ℝ) 1 → z ∈ E → z ∈ F) :
    scalarCropLaw ν ρ C E ≤ (ν C)⁻¹ * μ F := by
  have hsub' : E ∩ C ×ˢ univ ≤ᵐ[μ] F := by
    filter_upwards [hunit] with z hz
    intro he
    exact hsub z he.2.1 hz he.1
  change ((ν C)⁻¹ • ρ.restrict (C ×ˢ univ)) E ≤ _
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (hC.prod MeasurableSet.univ)]
  exact mul_le_mul' le_rfl ((hρ _).trans (measure_mono_ae hsub'))

end

end Submission.Obl.k4_general_parent_projected_layers
