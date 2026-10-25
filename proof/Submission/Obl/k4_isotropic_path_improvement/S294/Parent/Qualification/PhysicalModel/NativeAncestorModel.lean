-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeAncestorModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct.BoundedPacketModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ResidualOscillation

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
    (root : Fin p.C)

def coefficientBound (Vmax : ℝ) : ℝ := p.κ+24*p.κ+p.κ^2+Vmax

include hp

theorem coefficientBound_nonneg {Vmax : ℝ} (hVmax : 0 ≤ Vmax) :
    0 ≤ coefficientBound (p:=p) Vmax := by
  have hκ : 0 ≤ p.κ := zero_le_one.trans hp.1
  dsimp only [coefficientBound]
  positivity

/-- The ancestor's literal normalized remainder on the full original
assignment, with a globally bounded coefficient table. Its prior is
unchanged even outside the eventual source. -/
def model (Vmax : ℝ) (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root) :
    PhysicalModel :=
  Direct.boundedPacketModel (hp.frozenPacket root)
    (ParentSignal.clockPacketCoefficients (SignalGraph.ancestorSignal (d.N k) p root) p root)
    (ParentSignal.measurable_clockPacketCoefficients _ _ _)
    (coefficientBound (p:=p) Vmax) (coefficientBound_nonneg hp hVmax)
    source hsource hsourceF

variable {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)

theorem model_prior (ν : Measure Ln) :
    (model hp root Vmax hVmax source hsource hsourceF).prior ν=(hp.frozenPacket root).prior ν :=
  Direct.boundedPacketModel_prior _ _ _ _ _ _ _ _ ν

theorem model_prior_probability (hd : d.Valid) :
    IsProbabilityMeasure ((model hp root Vmax hVmax source hsource hsourceF).prior
      (d.ν k (p.γ root))) := by
  haveI : IsProbabilityMeasure (d.ν k (p.γ root)) := (hd.weights k).2.2 _
  rw [model_prior]
  exact hp.frozenPacket_prior_probability (by linarith [hd.1 k]) root

theorem model_global_coefficients (l : Ln) (i : Fin 7) :
    |(model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients l i| ≤
      coefficientBound (p:=p) Vmax :=
  Direct.boundedPacketModel_jets _ _ _ _ _ _ _ _ l i

include hsourceF in
theorem source_coefficients (hR : (p.R root).totalDegree ≤ 2)
    (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax) :
    ∀ z∈source, ∀ i,
      |ParentSignal.clockPacketCoefficients (SignalGraph.ancestorSignal (d.N k) p root)
        p root z.1 i| ≤ coefficientBound (p:=p) Vmax := by
  intro z hz i
  have hA : z.1∈p.A root := ((hp.frozenPacket root).counted_inside_original (hsourceF hz)).2.1
  exact SignalGraph.ancestor_good_coefficients hp root hR z.1 ⟨hA,hvelocity z hz⟩ hA i

theorem model_coefficients (hR : (p.R root).totalDegree ≤ 2)
    (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax) {z : Ev}
    (hz : z∈(model hp root Vmax hVmax source hsource hsourceF).event) :
    (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients z.1=
      ParentSignal.clockPacketCoefficients (SignalGraph.ancestorSignal (d.N k) p root) p root z.1 :=
  Direct.boundedPacketModel_coefficients _ _ _ _ _ _ _ _
    (source_coefficients hp root source hsourceF hR hvelocity) hz

/-- On the full original prior, clipping changes no coefficient atom.
The only almost-everywhere input is the problem's original velocity bound. -/
theorem model_coefficients_ae (hd : d.Valid) (hR : (p.R root).totalDegree ≤ 2)
    (hVlarge : d.K k ≤ Vmax) :
    ∀ᵐ l ∂(hp.frozenPacket root).prior (d.ν k (p.γ root)),
      (model hp root Vmax hVmax source hsource hsourceF).scalarCoefficients l=
        ParentSignal.clockPacketCoefficients (SignalGraph.ancestorSignal (d.N k) p root) p root l := by
  apply Direct.boundedPacketModel_coefficients_ae
  filter_upwards [hd.native_bounds k (p.γ root)] with l hl
  intro hA
  have hvel : ‖v l‖ ≤ Vmax :=
    ((le_add_of_nonneg_left (norm_nonneg _)).trans (hl 0 ⟨le_rfl,zero_le_one⟩)).trans hVlarge
  exact SignalGraph.ancestor_good_coefficients hp root hR l ⟨hA,hvel⟩ hA

/-- The actual graph clock code of the ancestor and the qualification
model's fine code agree on every source incidence. -/
theorem model_code (hR : (p.R root).totalDegree ≤ 2)
    (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax) {x : Ev} (hx : x∈source) (base hidden : ℝ) :
    Graph.modelCode (model hp root Vmax hVmax source hsource hsourceF) base hidden
      ((hp.frozenPacket root).timeChange x)=
        fun j => ⌊clockParentCoordinates p root (SignalGraph.ancestorSignal (d.N k) p root) x j /
          (if j=3 then hidden else base)⌋ := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  have hz : (hp.frozenPacket root).timeChange x∈pm.event := ⟨x,hx,rfl⟩
  have hA := pm.event_assignment _ hz
  have hc := model_coefficients hp root hVmax source hsource hsourceF hR hvelocity hz
  have hpoint := ParentSignal.clockPacket_point (SignalGraph.ancestorSignal_totalDegree (d.N k) p root hR)
    p root x
  rw [Graph.clock_timeChange hp root x] at hA hc ⊢
  funext j
  simp only [Graph.modelCode,ParentSource.Broad.Source.Jets2.coefficientGridCode]
  rw [Graph.modelCoefficients_of_mem pm hA,hc]
  change ⌊ParentSource.Broad.Source.Jets2.coefficientPhysical
    (ParentSignal.clockPacketCoefficients (SignalGraph.ancestorSignal (d.N k) p root) p root x.1)
      (packetTime p root x) j/(if j=3 then hidden else base)⌋=_
  rw [hpoint]
  congr 2
  fin_cases j <;> rfl

/-- In particular, the graph rows and qualification model use the same
literal fine state at equal base and signal mesh. -/
theorem model_clock_code (hR : (p.R root).totalDegree ≤ 2)
    (hvelocity : ∀ z∈source, ‖v z.1‖ ≤ Vmax) {x : Ev} (hx : x∈source) (mesh : ℝ) :
    Graph.modelCode (model hp root Vmax hVmax source hsource hsourceF) mesh mesh
      ((hp.frozenPacket root).timeChange x)=
        clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh x := by
  rw [model_code hp root hVmax source hsource hsourceF hR hvelocity hx]
  funext j
  simp only [ite_self]
  rfl

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
