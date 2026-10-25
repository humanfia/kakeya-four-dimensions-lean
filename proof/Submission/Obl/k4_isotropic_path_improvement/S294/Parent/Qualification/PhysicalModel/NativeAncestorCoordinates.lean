-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.HereditaryTables
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PencilFromStrips

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native

noncomputable section

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0≤Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree≤2)
    (hvelocity : ∀ z∈source, ‖v z.1‖≤Vmax)

include hp hR hvelocity

/-- The globally bounded model retains the actual ORIGINAL velocity
at every selected incidence, with no packet shear or velocity rescaling. -/
theorem model_velocity {x : Ev} (hx : x∈source) :
    Jets2.zv ((model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients x.1)=
      fun i => v x.1 i := by
  have hz : (hp.frozenPacket root).timeChange x∈
      (model hp root Vmax hVmax source hsource hsourceF).event := ⟨x,hx,rfl⟩
  have hc := model_coefficients hp root hVmax source hsource hsourceF hR hvelocity hz
  rw [Graph.clock_timeChange hp root x] at hc
  rw [hc]
  exact ParentSignal.clockPacket_velocity _ p root x.1

/-- The signal and the base used by scalar support are the actual
ancestor clock coordinates, pointwise on the unchanged source. -/
theorem model_originalPoint {x : Ev} (hx : x∈source) :
    (model hp root Vmax hVmax source hsource hsourceF).originalPoint
      ((hp.frozenPacket root).timeChange x)=
        fun j => clockParentCoordinates p root (SignalGraph.ancestorSignal (d.N k) p root) x j := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  have hz : (hp.frozenPacket root).timeChange x∈pm.event := ⟨x,hx,rfl⟩
  have hc := model_coefficients hp root hVmax source hsource hsourceF hR hvelocity hz
  have hpoint := ParentSignal.clockPacket_point
    (SignalGraph.ancestorSignal_totalDegree (d.N k) p root hR) p root x
  rw [Graph.clock_timeChange hp root x] at hc ⊢
  funext j
  change originalPhysicalCoordinates (pm.signal x.1) (pm.position x.1) (pm.velocity x.1)
    (packetTime p root x) j=_
  rw [pm.physical_scalar_coord,hc]
  have h := congrArg (fun y : EuclideanSpace ℝ (Fin 4) => y j) hpoint
  fin_cases j <;> exact h

/-- In particular the moving-band and census base is unchanged. -/
theorem model_originalBase {x : Ev} (hx : x∈source) :
    (model hp root Vmax hVmax source hsource hsourceF).originalBase
      ((hp.frozenPacket root).timeChange x)=unshearedPacketBase p root x := by
  ext j
  change (model hp root Vmax hVmax source hsource hsourceF).originalPoint
    ((hp.frozenPacket root).timeChange x) j.castSucc=_
  rw [model_originalPoint hp root hVmax source hsource hsourceF hR hvelocity hx]
  fin_cases j <;> rfl

/-- The planar vector in the pencil preparation is the same original
velocity that appears in retained-record strip caps. -/
theorem model_planarVelocityVector {x : Ev} (hx : x∈source) :
    (model hp root Vmax hVmax source hsource hsourceF).planarVelocityVector x.1=v x.1 := by
  have h := model_velocity hp root hVmax source hsource hsourceF hR hvelocity hx
  ext j
  exact congrFun h j

omit hvelocity in
/-- The same velocity identity holds on the FULL original prior. -/
theorem model_velocity_ae (hd : d.Valid) (hVlarge : d.K k≤Vmax) :
    ∀ᵐ l ∂(hp.frozenPacket root).prior (d.ν k (p.γ root)),
      Jets2.zv ((model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients l)=
        fun i => v l i := by
  filter_upwards [model_coefficients_ae hp root hVmax source hsource hsourceF hd hR hVlarge]
    with l hl
  rw [hl]
  exact ParentSignal.clockPacket_velocity _ p root l

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
