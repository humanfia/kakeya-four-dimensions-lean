-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ResidualOscillation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ResidualOscillation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenResidualOscillation.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenResidualOscillation.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ResidualRange
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PacketStrips
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalResidualTables


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

def scalarStateToPhysical (q : Fin 4 → ℤ) : Fin 4 → ℤ := fun j => q (physicalIndex j)

def physicalStateToScalar (q : Fin 4 → ℤ) : Fin 4 → ℤ := fun j => q (![0,3,1,2] j)

theorem physicalStateToScalar_scalarStateToPhysical (q : Fin 4 → ℤ) :
    physicalStateToScalar (scalarStateToPhysical q)=q := by
  funext j
  fin_cases j <;> rfl

theorem scalarStateToPhysical_physicalStateToScalar (q : Fin 4 → ℤ) :
    scalarStateToPhysical (physicalStateToScalar q)=q := by
  funext j
  fin_cases j <;> rfl

theorem physicalIndex_surjective : Function.Surjective physicalIndex := by
  intro j
  fin_cases j
  · exact ⟨0,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

theorem scalarStateToPhysical_injective : Function.Injective scalarStateToPhysical := by
  intro q q' hq
  funext j
  obtain ⟨i,rfl⟩ := physicalIndex_surjective j
  exact congrFun hq i

/-- The scalar-normal cell is only a permutation of the ORIGINAL
native physical cell, so its full original fiber is identical. -/
theorem physicalState_eq_scalarState (p : PhysicalModel) (b : ℝ) (z : Ev) :
    p.physicalState b z=scalarStateToPhysical (Jets2.originalFineState p.scalarCoefficients b z) := by
  funext j
  change ⌊originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 j/b⌋ =
    ⌊Jets2.zpos (p.scalarCoefficients z.1) z.2 (physicalIndex j)/b⌋
  rw [p.physical_scalar_coord]

theorem scalarState_eq_physicalState (p : PhysicalModel) (b : ℝ) (z : Ev) :
    Jets2.originalFineState p.scalarCoefficients b z=physicalStateToScalar (p.physicalState b z) := by
  rw [p.physicalState_eq_scalarState,physicalStateToScalar_scalarStateToPhysical]

theorem original_scalar_state_fiber (p : PhysicalModel) (b : ℝ) (q : Fin 4 → ℤ) :
    (Jets2.originalFineState p.scalarCoefficients b) ⁻¹' {q} =
      (p.physicalState b) ⁻¹' {scalarStateToPhysical q} := by
  ext z
  simp only [mem_preimage,mem_singleton_iff,p.physicalState_eq_scalarState,
    scalarStateToPhysical_injective.eq_iff]

/-- Actual old graph error and actual row approximation give the tiny
within-entry oscillation required by the residual preparation factory.
The coefficients, time gap, old physical state and parameter-world
center are all the literal original ones. -/
theorem original_canonical_residual_oscillation (p : PhysicalModel)
    (E : Set Ev) (hEp : E ⊆ p.event)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (b ρ K η error : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hK : 1 ≤ K) (hpacket : 17*p.slack ≤ K) (hη : 0 ≤ η)
    (hrow : ∀ z∈E, ∀ i : Fin 2,
      |G (p.physicalState b z) i.succ-F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2 i| ≤ η)
    (hgraph : ∀ z∈E,
      |(p.signal z.1).derivative.eval z.2-∑ j, G (p.physicalState b z) j*p.velocity z.1 j| ≤ error) :
    ∀ z∈E, ∀ z'∈E,
      Jets2.originalFineState p.scalarCoefficients b z=Jets2.originalFineState p.scalarCoefficients b z' →
      Jets2.parameterCode ρ (p.scalarCoefficients z.1)=Jets2.parameterCode ρ (p.scalarCoefficients z'.1) →
      |Jets2.originalResidualValue (fun y => Jets2.canonicalZoomCoefficients p.scalarCoefficients ρ y.1)
        (fun y => F (Jets2.parameterCode ρ (p.scalarCoefficients y.1)) y.2) Prod.snd z -
        Jets2.originalResidualValue (fun y => Jets2.canonicalZoomCoefficients p.scalarCoefficients ρ y.1)
          (fun y => F (Jets2.parameterCode ρ (p.scalarCoefficients y.1)) y.2) Prod.snd z'| ≤
            (2*(error+2*η*ρ)+2*(K+1)*b)/ρ := by
  intro z hz z' hz' hstate hworld
  let q := Jets2.parameterCode ρ (p.scalarCoefficients z.1)
  let Ew : Set Ev := {y∈E | Jets2.parameterCode ρ (p.scalarCoefficients y.1)=q}
  let center := Jets2.parameterCenter ρ q
  have hcoeff (y : Ev) (hy : y∈E) (i : Fin 7) : |p.scalarCoefficients y.1 i| ≤ K :=
    (p.scalar_coefficients_bound y.1 (p.event_assignment y (hEp hy)) i).trans hpacket
  have hcenter : |center 2| ≤ K+1 :=
    Jets2.original_parameter_center_bound ρ K hρ hρ1 (p.scalarCoefficients z.1) (hcoeff z hz) 2
  have hdiam (y : Ev) (hy : y∈Ew) (i : Fin 7) :
      |p.scalarCoefficients y.1 i-center i| ≤ ρ := by
    have hh := Jets2.original_parameter_center_distance ρ hρ (p.scalarCoefficients y.1) i
    simpa only [hy.2] using hh
  have hrow' (y : Ev) (hy : y∈Ew) (i : Fin 2) :
      |G (p.physicalState b y) i.succ-F q y.2 i| ≤ η := by
    simpa only [hy.2] using hrow y hy.1 i
  have hphysical : p.physicalState b z=p.physicalState b z' := by
    rw [p.physicalState_eq_scalarState,p.physicalState_eq_scalarState,hstate]
  have hh := p.original_fine_state_residual_range Ew G center (F q) b ρ (K+1) η error
    hb hρ (by linarith) hη hcenter hdiam hrow' (fun y hy => hgraph y hy.1)
    z ⟨hz,rfl⟩ z' ⟨hz',hworld.symm⟩ hphysical
  have hworld' : Jets2.parameterCode ρ (p.scalarCoefficients z'.1)=q := hworld.symm
  simpa only [Jets2.originalResidualValue,Jets2.canonicalZoomCoefficients,
    hworld',q,center,Jets2.zR] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
