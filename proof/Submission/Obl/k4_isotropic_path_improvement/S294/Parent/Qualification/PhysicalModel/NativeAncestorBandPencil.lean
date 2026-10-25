-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorBandPencil, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockIncidenceCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open scoped ENNReal RealInnerProductSpace

noncomputable section

theorem measurable_planarVelocityVector (pm : PhysicalModel) : Measurable pm.planarVelocityVector := by
  unfold planarVelocityVector
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · change Measurable (fun l => pm.scalarCoefficients l 4)
    exact (measurable_pi_apply 4).comp pm.measurable_scalarCoefficients
  · change Measurable (fun l => pm.scalarCoefficients l 6)
    exact (measurable_pi_apply 6).comp pm.measurable_scalarCoefficients

namespace NativeAncestor
section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0≤Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree≤2)
    (hvelocity : ∀ z∈source, ‖v z.1‖≤Vmax)

include hp hR hvelocity

/-- The scalar-support fine state is the actual ancestor graph code. -/
theorem model_physicalState {x : Ev} (hx : x∈source) (mesh : ℝ) :
    (model hp root Vmax hVmax source hsource hsourceF).physicalState mesh
      ((hp.frozenPacket root).timeChange x)=
        clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh x := by
  funext j
  change ⌊(model hp root Vmax hVmax source hsource hsourceF).originalPoint
    ((hp.frozenPacket root).timeChange x) j/mesh⌋=_
  rw [model_originalPoint hp root hVmax source hsource hsourceF hR hvelocity hx]
  rfl

omit hR hvelocity in
/-- The actual bounded ancestor model meets the scalar-support slack bound. -/
theorem model_slack_one_le : 1≤(model hp root Vmax hVmax source hsource hsourceF).slack := by
  change 1≤coefficientBound (p:=p) Vmax
  have hκ : 0≤p.κ := zero_le_one.trans hp.1
  dsimp only [coefficientBound]
  nlinarith [hp.1,sq_nonneg p.κ]

/-- The normalized scalar rate is the original ancestor rate in its
literal signal-over-clock units. -/
theorem model_rate {x : Ev} (hx : x∈source) :
    ((model hp root Vmax hVmax source hsource hsourceF).signal
      ((hp.frozenPacket root).timeChange x).1).derivative.eval ((hp.frozenPacket root).timeChange x).2=
        (((2:ℝ)^p.T (p.lev root))⁻¹/δ (d.N k) (p.r (p.lev root)))*
          Submission.Lib.K4GlobalParentSignal.rate (p.R root) x.1 x.2 := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  have hz : (hp.frozenPacket root).timeChange x∈pm.event := ⟨x,hx,rfl⟩
  have hc := model_coefficients hp root hVmax source hsource hsourceF hR hvelocity hz
  rw [Graph.clock_timeChange hp root x] at hc ⊢
  rw [←pm.scalar_x_derivative,hc]
  exact (ParentSignal.clockPacket_rate
    (SignalGraph.ancestorSignal_totalDegree (d.N k) p root hR) p root x).trans
      (SignalGraph.rate_ancestorSignal (d.N k) p root x.1 x.2)

/-- Actual original moving-band numerators give precisely the band
input used by scalar support in the native model's full-prior clock. -/
theorem model_moving_band_cap
    (ν : Measure Ln) [IsFiniteMeasure ν] (hA : ν (p.A root)≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (U : Set P3) (hU : MeasurableSet U) (center : P3 → ℝ) (hcenter : Measurable center)
    (width : ℝ) (cap : ENNReal)
    (hcap : ((ν.prod volume).restrict S) {z | unshearedPacketBase p root z∈U ∧
      |physicalParentSignal (d.N k) p root (p.R root) z-center (unshearedPacketBase p root z)|≤width}≤
        cap*(ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*ν (p.A root))) :
    (hp.frozenPacket root).selectedLaw ν S {z |
      (model hp root Vmax hVmax source hsource hsourceF).originalBase z∈U ∧
      |(model hp root Vmax hVmax source hsource hsourceF).originalPoint z 3-
        center ((model hp root Vmax hVmax source hsource hsourceF).originalBase z)|≤width}≤cap := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let clock : Ev → P3×ℝ := fun z => (pm.originalBase z,pm.originalPoint z 3)
  let original : Ev → P3×ℝ := fun z =>
    (unshearedPacketBase p root z,physicalParentSignal (d.N k) p root (p.R root) z)
  have hclock : Measurable clock := pm.measurable_originalBase.prodMk
    ((measurable_pi_apply 3).comp pm.measurable_originalPoint)
  have hcoordinates : ∀ z∈S, clock ((hp.frozenPacket root).timeChange z)=original z := by
    intro z hz
    exact Prod.ext (model_originalBase hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz))
      (model_hidden_coordinate hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz))
  let B : Set (P3×ℝ) := {a | a.1∈U ∧ |a.2-center a.1|≤width}
  have hB : MeasurableSet B := (measurable_fst hU).inter
    (measurableSet_le ((measurable_snd.sub (hcenter.comp measurable_fst)).abs) measurable_const)
  exact selected_clock_coordinate_cap_of_original (hp.frozenPacket root) ν hA S hS
    (hSsource.trans hsourceF) clock original hclock hcoordinates B hB cap hcap

/-- Original statewise strip ratios pass to the model's exact physical
fine states, with their original current denominators. -/
theorem model_state_strip_cap
    (ν : Measure Ln) [IsFiniteMeasure ν] (hA : ν (p.A root)≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (mesh : ℝ) (cell : Fin 4 → ℤ) (normal : P2) (offset width : ℝ) (cap : ENNReal)
    (hcap : ((ν.prod volume).restrict S) {z |
      clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z=cell ∧
      |inner ℝ normal (v z.1)-offset|≤width}≤cap*((ν.prod volume).restrict S)
        (clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh ⁻¹' {cell})) :
    (hp.frozenPacket root).selectedLaw ν S {z |
      (model hp root Vmax hVmax source hsource hsourceF).physicalState mesh z=cell ∧
      |inner ℝ normal ((model hp root Vmax hVmax source hsource hsourceF).planarVelocityVector z.1)-offset|≤width}≤
      cap*(hp.frozenPacket root).selectedLaw ν S
        ((model hp root Vmax hVmax source hsource hsourceF).physicalState mesh ⁻¹' {cell}) := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let clock : Ev → (Fin 4 → ℤ)×P2 := fun z => (pm.physicalState mesh z,pm.planarVelocityVector z.1)
  let original : Ev → (Fin 4 → ℤ)×P2 := fun z =>
    (clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z,v z.1)
  have hclock : Measurable clock := (pm.measurable_physicalState mesh).prodMk
    (pm.measurable_planarVelocityVector.comp measurable_fst)
  have hcoordinates : ∀ z∈S, clock ((hp.frozenPacket root).timeChange z)=original z := by
    intro z hz
    apply Prod.ext
    · exact model_physicalState hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz) mesh
    · change pm.planarVelocityVector ((hp.frozenPacket root).timeChange z).1=v z.1
      rw [Graph.clock_timeChange hp root z,
        model_planarVelocityVector hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz)]
  let B : Set ((Fin 4 → ℤ)×P2) := {a | a.1=cell ∧ |inner ℝ normal a.2-offset|≤width}
  let D : Set ((Fin 4 → ℤ)×P2) := {a | a.1=cell}
  have hD : MeasurableSet D := measurable_fst (measurableSet_singleton cell)
  have hB : MeasurableSet B := hD.inter
    (measurableSet_le (((measurable_const.inner measurable_snd).sub_const offset).abs) measurable_const)
  exact selected_clock_coordinate_ratio_of_original (hp.frozenPacket root) ν hA S hS
    (hSsource.trans hsourceF) clock original hclock hcoordinates B D hB hD cap hcap

/-- The genuine original graph-code strip caps construct the exact
normalized-pencil premise of scalar support, with no pencil oracle. -/
theorem model_pencil_bound_of_original_strips
    (ν : Measure Ln) [IsFiniteMeasure ν] (hA : ν (p.A root)≠0)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    {mesh width radius failure : ℝ} (hradius : 0≤radius)
    (hwidth : 2*(Vmax+1)*((Vmax+1)*radius)≤width)
    (hsmall : (Vmax+1)*radius≤1/4)
    (hstrip : ∀ cell (normal : P2) offset, ‖normal‖=1 →
      ((ν.prod volume).restrict S) {z |
        clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z=cell ∧
        |inner ℝ normal (v z.1)-offset|≤width}≤ENNReal.ofReal failure*((ν.prod volume).restrict S)
          (clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh ⁻¹' {cell})) :
    ∀ cell (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V<3 →
      (hp.frozenPacket root).selectedLaw ν S {z |
        (model hp root Vmax hVmax source hsource hsourceF).physicalState mesh z=cell ∧
        Metric.infDist (NativeAssigned.direction
          ((model hp root Vmax hVmax source hsource hsourceF).baseVelocityVector z.1)) (V : Set _) < radius}≤
          ENNReal.ofReal failure*(hp.frozenPacket root).selectedLaw ν S
            ((model hp root Vmax hVmax source hsource hsourceF).physicalState mesh ⁻¹' {cell}) := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  apply pm.pencil_bound_of_current_strip_caps ((hp.frozenPacket root).selectedLaw ν S)
    hVmax hradius hwidth hsmall ?_ ?_
  · apply (ae_restrict_mem ((hp.frozenPacket root).measurable_selectedEvent hS)).mono
    rintro z ⟨x,hx,rfl⟩
    rw [Graph.clock_timeChange hp root x,
      model_planarVelocityVector hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx)]
    exact hvelocity x (hSsource hx)
  · intro cell normal offset hnormal
    exact model_state_strip_cap hp root hVmax source hsource hsourceF hR hvelocity
      ν hA S hS hSsource mesh cell normal offset width (ENNReal.ofReal failure) (hstrip cell normal offset hnormal)

end Path
end NativeAncestor

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
