-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalDyadicPhysicalCensus

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open Submission.Lib.K4ParentSignalPreparation.Census

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

/-- The hidden coordinate used by scalar support is literally the
original normalized remainder of the actual ancestor. -/
theorem model_hidden_coordinate {x : Ev} (hx : x∈source) :
    (model hp root Vmax hVmax source hsource hsourceF).originalPoint
      ((hp.frozenPacket root).timeChange x) 3=
        physicalParentSignal (d.N k) p root (p.R root) x := by
  rw [model_originalPoint hp root hVmax source hsource hsourceF hR hvelocity hx]
  change clockParentSignal p root (SignalGraph.ancestorSignal (d.N k) p root) x=_
  simpa only [one_mul] using (SignalGraph.ancestorSignal_clock (d.N k) p root x).symm

/-- The clock model's occupied census is exactly the actual ancestor
census, including after arbitrary source restrictions. There is no
extra support envelope or cardinality loss in changing clocks. -/
theorem model_occupied (S : Set Ev) (hSsource : S⊆source) (base hidden theta : ℝ) :
    occupied ((hp.frozenPacket root).selectedEvent S)
      (fun z j => (model hp root Vmax hVmax source hsource hsourceF).originalBase z j)
      (fun z => (model hp root Vmax hVmax source hsource hsourceF).originalPoint z 3/theta)
      base hidden=
    occupied S (fun z j => unshearedPacketBase p root z j)
      (fun z => physicalParentSignal (d.N k) p root (p.R root) z/theta) base hidden := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  have hcode (z : Ev) (hz : z∈S) :
      gridCode (fun z j => pm.originalBase z j) (fun z => pm.originalPoint z 3/theta)
        base hidden ((hp.frozenPacket root).timeChange z)=
      gridCode (fun z j => unshearedPacketBase p root z j)
        (fun z => physicalParentSignal (d.N k) p root (p.R root) z/theta) base hidden z := by
    dsimp only [gridCode,pm]
    rw [model_originalBase hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz),
      model_hidden_coordinate hp root hVmax source hsource hsourceF hR hvelocity (hSsource hz)]
  ext q
  constructor
  · rintro ⟨z,⟨x,hx,rfl⟩,hq⟩
    exact ⟨x,hx,(hcode x hx).symm.trans hq⟩
  · rintro ⟨x,hx,hq⟩
    exact ⟨(hp.frozenPacket root).timeChange x,⟨x,hx,rfl⟩,(hcode x hx).trans hq⟩

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
