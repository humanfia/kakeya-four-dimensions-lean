-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenStripSupport.lean.
The bounded quadratic physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenStripSupport.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PacketStrips
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.StripAnchors
import Submission.Obl.k4_scalar_heavy_intercept_selection.GroupPruning


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

def stripLabel (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) : Ev → (Fin 4 → ℤ) × ℤ :=
  originalStripLabel b ρ width row p.signal p.position p.velocity

theorem measurable_stripLabel (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) : Measurable (p.stripLabel b ρ width row) :=
  measurable_originalStripLabel b ρ width row p.signal p.position p.velocity
    p.measurable_physical_coordinates

def stripSupport (p : PhysicalModel) (E : Set Ev) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) : Set Ln :=
  originalOccupationSupport volume (originalStripDensity E (p.stripLabel b ρ width row) i)

theorem measurableSet_stripSupport (p : PhysicalModel) {E : Set Ev} (hE : MeasurableSet E)
    (b ρ width : ℝ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) :
    MeasurableSet (p.stripSupport E b ρ width row i) :=
  measurableSet_originalOccupationSupport volume
    (measurable_originalStripDensity hE _ (p.measurable_stripLabel b ρ width row) i)

/-- Every supporting ORIGINAL line has an actual old strip occurrence,
with exactly the same original trajectory index. -/
theorem stripSupport_witness (p : PhysicalModel) (E : Set Ev) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) (l : Ln)
    (hl : l ∈ p.stripSupport E b ρ width row i) :
    ∃ t : ℝ, (l,t) ∈ E ∧ p.stripLabel b ρ width row (l,t) = i := by
  obtain ⟨t, ht⟩ := exists_original_occupation volume
    (originalStripDensity E (p.stripLabel b ρ width row) i) l hl
  exact ⟨t, (originalStripDensity_ne_zero E _ i (l,t)).mp ht⟩

theorem stripLabel_coarse (p : PhysicalModel) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (z : Ev) :
    (p.stripLabel b ρ width row z).1 =
      roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2) := rfl

/-- Positive old occupation bounds the whole affine line's normalized
anchor. This bound is valid on the supporting ORIGINAL line prior. -/
theorem stripSupport_anchor_bound (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    {E : Set Ev} (hEp : E ⊆ p.event) {b ρ : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ) (width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ)
    (l : Ln) (hl : l ∈ p.stripSupport E b ρ width row i) (j : Fin 3) :
    |normalizedStripAnchor (p.position l) (p.velocity l) ρ i.1 j| ≤ 2 + 34 * p.slack := by
  obtain ⟨t, ht, hlabel⟩ := p.stripSupport_witness E b ρ width row i l hl
  have hassigned : l ∈ p.assigned := p.event_assignment (l,t) (hEp ht)
  have hcoarse := congrArg Prod.fst hlabel
  rw [p.stripLabel_coarse] at hcoarse
  have h := normalizedStripAnchor_bound hb hρ hbρ (by linarith : 0 ≤ 17 * p.slack)
    (p.signal l) (p.position l) (p.velocity l) rfl (p.velocity_time l)
    (p.velocity_bound hκ l hassigned) i.1 t hcoarse j
  simpa only [show 2 * (17 * p.slack) = 34 * p.slack by ring] using h

/-- The actual law in one strip is dominated by the product of time
and that strip's ORIGINAL supporting trajectory prior. The density
factor is exactly the preceding original factor. -/
theorem strip_original_prior_domination (p : PhysicalModel) (ν : Measure Ln)
    [IsFiniteMeasure (p.prior ν)] (μ : Measure Ev) (K : ENNReal)
    {E : Set Ev} (hE : MeasurableSet E) (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (hdom : μ ≤ K • (p.prior ν).prod volume)
    (b ρ width : ℝ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) :
    μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {i}) ≤
      K • ((p.prior ν).restrict (p.stripSupport E b ρ width row i)).prod volume := by
  apply Submission.Obl.k4_scalar_heavy_intercept_selection.prior_restriction_domination
    (p.prior ν) _ K _ (p.measurableSet_stripSupport hE b ρ width row i)
    (Measure.restrict_le_self.trans hdom)
  exact ae_original_strip_support (p.prior ν) volume μ K hE
    _ (p.measurable_stripLabel b ρ width row) hdom hfull i

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
