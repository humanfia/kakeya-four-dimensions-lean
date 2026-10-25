-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorPureCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockIncidenceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentOriginalFloorCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open scoped ENNReal

noncomputable section

/-- The scalar cleanup base has the model's literal original coordinates. -/
theorem scalar_originalBaseCoordinates (pm : PhysicalModel) (z : Ev) :
    Jets2.originalBaseCoordinates pm.scalarCoefficients z=fun i => pm.originalBase z i := by
  funext i
  change _=originalPhysicalCoordinates (pm.signal z.1) (pm.position z.1) (pm.velocity z.1) z.2 i.castSucc
  rw [pm.physical_scalar_coord]
  fin_cases i <;> rfl

theorem scalar_originalSignal (pm : PhysicalModel) (z : Ev) :
    Jets2.zx (pm.scalarCoefficients z.1) z.2=pm.originalPoint z 3 := by
  change _=originalPhysicalCoordinates (pm.signal z.1) (pm.position z.1) (pm.velocity z.1) z.2 3
  rw [pm.physical_scalar_coord]
  rfl

namespace NativeAncestor

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0≤Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree≤2)
    (hvelocity : ∀ z∈source, ‖v z.1‖≤Vmax)

include hR hvelocity

/-- Actual original pure joint-cell numerators supply the exact scalar
pure-cell caps used to construct original coefficient floors. The
normalization cancels ONLY the full ancestor reference; palette weights
are unchanged, including on every later measurable source restriction. -/
theorem model_scalar_pure_cap
    (ν : Measure Ln) [IsFiniteMeasure ν] (hA : ν (p.A root)≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (base hidden velocityMesh : ℝ) (b : Fin 3 → ℤ) (j : ℤ)
    (D : Set (Fin 2 → ℤ)) (hD : MeasurableSet D) (cap : ENNReal)
    (hcap : ((ν.prod volume).restrict S) {z |
      (fun i => ⌊unshearedPacketBase p root z i/base⌋)=b ∧
      ⌊physicalParentSignal (d.N k) p root (p.R root) z/hidden⌋=j ∧
      Jets2.parameterCode velocityMesh (fun i => v z.1 i)∈D} ≤
        cap*(ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*ν (p.A root))) :
    (hp.frozenPacket root).selectedLaw ν S {z |
      Jets2.originalBaseCode (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients base z=b ∧
      ⌊Jets2.zx ((model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients z.1) z.2/hidden⌋=j ∧
      Jets2.vbin velocityMesh
        ((model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients z.1)∈D} ≤ cap := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let clock : Ev → ((Fin 3 → ℤ)×ℤ)×(Fin 2 → ℤ) := fun z =>
    ((Jets2.originalBaseCode pm.scalarCoefficients base z,⌊Jets2.zx (pm.scalarCoefficients z.1) z.2/hidden⌋),
      Jets2.vbin velocityMesh (pm.scalarCoefficients z.1))
  let original : Ev → ((Fin 3 → ℤ)×ℤ)×(Fin 2 → ℤ) := fun z =>
    (((fun i => ⌊unshearedPacketBase p root z i/base⌋),
      ⌊physicalParentSignal (d.N k) p root (p.R root) z/hidden⌋),
      Jets2.parameterCode velocityMesh (fun i => v z.1 i))
  have hc := pm.measurable_scalarCoefficients
  have hbase : Measurable (Jets2.originalBaseCode pm.scalarCoefficients base) := by
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> dsimp only [Jets2.originalBaseCode,Jets2.originalBaseCoordinates,Jets2.zy] <;> fun_prop
  have hclock : Measurable clock := by
    apply (hbase.prodMk ?_).prodMk ?_
    · unfold Jets2.zx
      fun_prop
    · apply (Jets2.measurable_parameterCode velocityMesh).comp
      unfold Jets2.zv
      fun_prop
  have hcoordinates : ∀ z∈S, clock ((hp.frozenPacket root).timeChange z)=original z := by
    intro z hz
    apply Prod.ext
    · apply Prod.ext
      · funext i
        change ⌊Jets2.originalBaseCoordinates pm.scalarCoefficients
          ((hp.frozenPacket root).timeChange z) i/base⌋=_
        rw [scalar_originalBaseCoordinates,
          model_originalBase hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz)]
      · change ⌊Jets2.zx (pm.scalarCoefficients ((hp.frozenPacket root).timeChange z).1)
          ((hp.frozenPacket root).timeChange z).2/hidden⌋=_
        rw [scalar_originalSignal,
          model_hidden_coordinate hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz)]
    · change Jets2.parameterCode velocityMesh
        (Jets2.zv (pm.scalarCoefficients ((hp.frozenPacket root).timeChange z).1))=_
      rw [Graph.clock_timeChange hp root z,
        model_velocity hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz)]
  let B : Set (((Fin 3 → ℤ)×ℤ)×(Fin 2 → ℤ)) := {a | a.1.1=b ∧ a.1.2=j ∧ a.2∈D}
  have hB : MeasurableSet B :=
    ((measurable_fst.comp measurable_fst) (measurableSet_singleton b)).inter
      (((measurable_snd.comp measurable_fst) (measurableSet_singleton j)).inter (measurable_snd hD))
  exact selected_clock_coordinate_cap_of_original (hp.frozenPacket root) ν hA S hS
    (hSsource.trans hsourceF) clock original hclock hcoordinates B hB cap hcap

end Path
end NativeAncestor

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
