-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripFilling, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripFilling.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenStripFilling.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenStripFilling.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripFrame
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssignedFilling
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WholeStateBreadth


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

def physicalState (p : PhysicalModel) (b : ℝ) (z : Ev) : Fin 4 → ℤ :=
  fun j => ⌊originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 j / b⌋

theorem measurable_physicalState (p : PhysicalModel) (b : ℝ) : Measurable (p.physicalState b) := by
  have h := p.measurable_physical_coordinates
  unfold physicalState
  fun_prop

theorem stripLabel_eq_state (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (z : Ev) :
    p.stripLabel b ρ width row z = nativeStripState b ρ width row (p.physicalState b z) := rfl

/-- A positive selected ORIGINAL strip fills actual three dimensional
base cells. The supporting prior, normalized affine frame, cell-time
ceiling, unit directions and whole-state breadth are constructed from
the same original packet and reference law. -/
theorem original_strip_base_filling (p : PhysicalModel) (ν : Measure Ln)
    [IsFiniteMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (K : NNReal) (hK : 0 < K)
    {E : Set Ev} (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z ∈ E) (hdom : μ ≤ K • (p.prior ν).prod volume)
    (b ρ width : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hw : 0 < width)
    (hbρ : b ≤ ρ) (hbw : b ≤ width) (hwρ : width ≤ ρ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (g : (Fin 4 → ℤ) × ℤ)
    (H δ failure C : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ)
    (hf0 : 0 ≤ failure) (hf1 : failure ≤ 1)
    (hC : 0 ≤ C) (hMK : FiniteMK 3 C)
    (hprior : (p.prior ν).real (p.stripSupport E b ρ width row g) ≤
      (H / ρ) * (μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {g})).real univ)
    (hmass : 0 < (μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {g})).real univ)
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z = q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure * μ ((p.physicalState b) ⁻¹' {q})) :
    ∃ F : Finset (Fin 3 → ℤ),
      (∀ᵐ z ∂μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {g}),
        NativeAssigned.code ρ b (width / ρ) (fun j => ρ * (g.1 j.castSucc : ℝ))
          (p.physicalState b z) ∈ F) ∧
      (∀ q ∈ F, (μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {g}))
        {z | NativeAssigned.code ρ b (width / ρ) (fun j => ρ * (g.1 j.castSucc : ℝ))
          (p.physicalState b z) = q} ≠ 0) ∧
      ((δ / 2) ^ 3 / 2 * (1 - failure) ^ 3) ≤
        (F.card : ℝ) * (8 * C * 7 ^ 3) ^ 2 * (3 * (K : ℝ) * H) ^ 3 * (width / ρ) ^ 3 := by
  classical
  let label := p.stripLabel b ρ width row
  let σ := μ.restrict (label ⁻¹' {g})
  let S := p.stripSupport E b ρ width row g
  let θ := (p.prior ν).restrict S
  let ξ := width / ρ
  let corner : Fin 3 → ℝ := fun j => ρ * (g.1 j.castSucc : ℝ)
  let coarse : (Fin 4 → ℤ) → Fin 3 → ℤ := NativeAssigned.code ρ b ξ corner
  let assigned : Ev → Fin 3 → ℤ := fun z => coarse (p.physicalState b z)
  let window := NativeAssigned.window ξ 2
  let F := Submission.Obl.k4_scalar_heavy_intercept_selection.positiveCodeWindow σ assigned window
  have hlabel : Measurable label := p.measurable_stripLabel b ρ width row
  have hS : MeasurableSet S := p.measurableSet_stripSupport hE b ρ width row g
  have hstate := p.measurable_physicalState b
  have hassigned : Measurable assigned := (NativeAssigned.measurable_code ρ b ξ corner).comp hstate
  have hξ : 0 < ξ := div_pos hw hρ
  have hξ₁ : ξ ≤ 1 := (div_le_one hρ).mpr hwρ
  have hscale : ρ * ξ = width := by dsimp [ξ]; field_simp
  have hbξ : b ≤ ρ * ξ := hbw.trans_eq hscale.symm
  have hdomENN : μ ≤ (K : ENNReal) • (p.prior ν).prod volume := by
    simpa only [Measure.coe_nnreal_smul] using hdom
  have hsupport : ∀ᵐ z ∂σ, z.1 ∈ S :=
    ae_original_strip_support (p.prior ν) volume μ (K : ENNReal) hE
      label hlabel hdomENN hfull g
  have hσdom : σ ≤ K • θ.prod volume := by
    have h := p.strip_original_prior_domination ν μ (K : ENNReal) hE hfull hdomENN b ρ width row g
    simpa only [Measure.coe_nnreal_smul] using h
  have hcarrier : ∀ᵐ z ∂σ, assigned z ∈ window := by
    have hg : ∀ᵐ z ∂σ, label z = g := ae_restrict_mem (hlabel (measurableSet_singleton g))
    filter_upwards [hg, ae_mono Measure.restrict_le_self hfull] with z hzg hzE
    have hcoarse := congrArg Prod.fst hzg
    rw [p.stripLabel_coarse] at hcoarse
    apply NativeAssigned.code_mem_window hρ hb hξ hξ₁ hbξ corner
      (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2)
    intro j
    have hj := physical_corner_bound hb hρ hbρ _ g.1 hcoarse j.castSucc
    change |(_ - ρ * (g.1 j.castSucc : ℝ)) / ρ| ≤ 2
    rw [abs_div, abs_of_pos hρ]
    exact (div_le_iff₀ hρ).mpr hj
  have hFcarrier : ∀ᵐ z ∂σ, assigned z ∈ F :=
    Submission.Obl.k4_scalar_heavy_intercept_selection.ae_mem_positiveCodeWindow
      σ σ le_rfl assigned hassigned window hcarrier
  have hFpositive (q : Fin 3 → ℤ) (hq : q ∈ F) : σ (assigned ⁻¹' {q}) ≠ 0 :=
    (Finset.mem_filter.mp hq).2
  have he : Measurable (fun z : Ev => NativeAssigned.direction (p.baseVelocityVector z.1)) :=
    NativeAssigned.measurable_direction.comp (p.measurable_baseVelocityVector.comp measurable_fst)
  have hbroad (q : Fin 3 → ℤ) (_hq : q ∈ F)
      (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hV : Module.finrank ℝ V < 3) :
      (1 - failure) * (σ.restrict {z | assigned z = q}).real univ ≤
        (σ.restrict {z | assigned z = q}).real
          {z | δ ≤ Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _)} := by
    have h := breadth_of_whole_group_cell μ (p.physicalState b) hstate
      (fun z => NativeAssigned.direction (p.baseVelocityVector z.1)) he δ failure hf0 hpencil
      (nativeStripState b ρ width row) coarse g q V hV
    simpa only [p.stripLabel_eq_state, σ, label, assigned,
      Set.preimage, Set.mem_singleton_iff] using h
  have hpriorθ : θ.real univ ≤ (H / ρ) * σ.real univ := by
    simpa only [θ, measureReal_def, Measure.restrict_apply_univ, σ, label] using hprior
  have hfill := NativeAssigned.assigned_base_filling θ σ K hK hC hMK hρ hb hξ hH hδ
    (by linarith : 0 ≤ 1 - failure) hbξ
    (p.stripAnchorVector E b ρ width row g) p.baseVelocityVector
    (p.measurable_stripAnchorVector hE b ρ width row g) p.measurable_baseVelocityVector
    p.baseVelocityVector_ne_zero (3 * (2 + 34 * p.slack))
    (p.stripAnchorVector_bound hκ hEp hb hρ hbρ width row g)
    S hS hsupport corner
    (fun z => originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2)
    p.measurable_physical_coordinates
    (fun z => originalPhysicalCoordinates_time _ _ _ rfl (p.velocity_time z.1) z.2)
    (by
      intro z hz j
      exact p.stripAnchorVector_motion E b width hρ row g z.1 hz z.2 j)
    hσdom hpriorθ hmass F hFcarrier hbroad
  exact ⟨F, hFcarrier, hFpositive, hfill⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
