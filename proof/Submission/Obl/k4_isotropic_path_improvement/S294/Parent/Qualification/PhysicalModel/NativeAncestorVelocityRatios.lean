-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorVelocityRatios, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorBandPencil

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open scoped ENNReal

noncomputable section

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree ≤ 2)
    (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax)

include hp hR hvelocity

/-- Current ORIGINAL graph-cell velocity-bin ratios transport exactly
to the native model, keeping the SAME palette and current denominator. -/
theorem model_current_velocity_ratio
    (ν : Measure Ln) [IsFiniteMeasure ν] (hA : ν (p.A root)≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (mesh velocityMesh : ℝ) (cell : Fin 4 → ℤ) (D : Set (Fin 2 → ℤ)) (hD : MeasurableSet D)
    (palette : Measure (Fin 2 → ℤ)) (C : ENNReal)
    (hcap : ((ν.prod volume).restrict S) {z |
      clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z=cell ∧
      Jets2.parameterCode velocityMesh (fun j => v z.1 j)∈D} ≤
        C*((ν.prod volume).restrict S)
          (clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh ⁻¹' {cell})*palette D) :
    (hp.frozenPacket root).selectedLaw ν S {z |
      (model hp root Vmax hVmax source hsource hsourceF).physicalState mesh z=cell ∧
      Jets2.parameterCode velocityMesh
        (Jets2.zv ((model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients z.1))∈D} ≤
      C*(hp.frozenPacket root).selectedLaw ν S
        ((model hp root Vmax hVmax source hsource hsourceF).physicalState mesh ⁻¹' {cell})*palette D := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let clock : Ev → (Fin 4 → ℤ)×(Fin 2 → ℤ) := fun z =>
    (pm.physicalState mesh z,Jets2.parameterCode velocityMesh (Jets2.zv (pm.scalarCoefficients z.1)))
  let original : Ev → (Fin 4 → ℤ)×(Fin 2 → ℤ) := fun z =>
    (clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z,
      Jets2.parameterCode velocityMesh (fun j => v z.1 j))
  have hclock : Measurable clock := (pm.measurable_physicalState mesh).prodMk (by
    apply (Jets2.measurable_parameterCode velocityMesh).comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · change Measurable (fun z : Ev => pm.scalarCoefficients z.1 4)
      exact (measurable_pi_apply 4).comp (pm.measurable_scalarCoefficients.comp measurable_fst)
    · change Measurable (fun z : Ev => pm.scalarCoefficients z.1 6)
      exact (measurable_pi_apply 6).comp (pm.measurable_scalarCoefficients.comp measurable_fst))
  have hcoords : ∀ z∈S, clock ((hp.frozenPacket root).timeChange z)=original z := by
    intro z hz
    apply Prod.ext
    · exact model_physicalState hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz) mesh
    · change Jets2.parameterCode velocityMesh
        (Jets2.zv (pm.scalarCoefficients ((hp.frozenPacket root).timeChange z).1))=_
      rw [Graph.clock_timeChange hp root z,
        model_velocity hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz)]
  let B : Set ((Fin 4 → ℤ)×(Fin 2 → ℤ)) := {a | a.1=cell ∧ a.2∈D}
  let A : Set ((Fin 4 → ℤ)×(Fin 2 → ℤ)) := {a | a.1=cell}
  have hAm : MeasurableSet A := measurable_fst (measurableSet_singleton cell)
  have hBm : MeasurableSet B := hAm.inter (measurable_snd hD)
  have hratio := selected_clock_coordinate_ratio_of_original (hp.frozenPacket root) ν hA S hS
    (hSsource.trans hsourceF) clock original hclock hcoords B A hBm hAm (C*palette D)
    (hcap.trans_eq (by ac_rfl))
  exact hratio.trans_eq (by ac_rfl)

/-- The scalar-normal original fine-state code is a permutation of the
same physical graph cell. Its current palette ratios are identical. -/
theorem model_original_fine_velocity_ratio
    (ν : Measure Ln) [IsFiniteMeasure ν] (hA : ν (p.A root)≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (mesh velocityMesh : ℝ) (cell : Fin 4 → ℤ) (D : Set (Fin 2 → ℤ)) (hD : MeasurableSet D)
    (palette : Measure (Fin 2 → ℤ)) (C : ENNReal)
    (hcap : ((ν.prod volume).restrict S) {z |
      clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z=scalarStateToPhysical cell ∧
      Jets2.parameterCode velocityMesh (fun j => v z.1 j)∈D} ≤
        C*((ν.prod volume).restrict S)
          (clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh ⁻¹' {scalarStateToPhysical cell})*palette D) :
    (hp.frozenPacket root).selectedLaw ν S {z |
      Jets2.originalFineState (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients mesh z=cell ∧
      Jets2.parameterCode velocityMesh
        (Jets2.zv ((model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients z.1))∈D} ≤
      C*(hp.frozenPacket root).selectedLaw ν S
        ((Jets2.originalFineState (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients mesh) ⁻¹' {cell})*
          palette D := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  have hcell (z : Ev) : Jets2.originalFineState pm.scalarCoefficients mesh z=cell ↔
      pm.physicalState mesh z=scalarStateToPhysical cell := by
    rw [pm.physicalState_eq_scalarState]
    exact scalarStateToPhysical_injective.eq_iff.symm
  change (hp.frozenPacket root).selectedLaw ν S {z |
    Jets2.originalFineState pm.scalarCoefficients mesh z=cell ∧
      Jets2.parameterCode velocityMesh (Jets2.zv (pm.scalarCoefficients z.1))∈D} ≤
    C*(hp.frozenPacket root).selectedLaw ν S
      ((Jets2.originalFineState pm.scalarCoefficients mesh) ⁻¹' {cell})*palette D
  rw [pm.original_scalar_state_fiber]
  simp_rw [hcell]
  exact model_current_velocity_ratio hp root hVmax source hsource hsourceF hR hvelocity
    ν hA S hS hSsource mesh velocityMesh (scalarStateToPhysical cell) D hD palette C hcap

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
