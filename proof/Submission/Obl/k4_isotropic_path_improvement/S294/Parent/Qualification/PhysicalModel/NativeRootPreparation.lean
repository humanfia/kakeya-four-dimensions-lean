-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.NativeRootPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootInput
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorBandPencil
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ClockIncidenceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalChildRowQualification

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open ParentSource ParentSource.Native
open scoped ENNReal BigOperators

noncomputable section

local instance (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section Path

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0  ≤  Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree  ≤  2)
    (hvelocity : ∀ z∈source, ‖v z.1‖  ≤  Vmax)

include hp hR hvelocity

/-- Complete native root preparation in the ORIGINAL incidence law.
The input record contains only literal primitive caps, floors, rows,
derivative lists and scale inequalities. The output is one whole
ancestor graph-code source, its row Lipschitz estimate and the exact
native exception relative to that final source. -/
theorem prepare_native_root_qualification
    (hd : d.Valid) (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (level : ℕ)
    (hend : ∀ z∈S, z∉p.oldEndpoints root ∧ z∉p.levelEndpoints level)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (graphMesh : ℝ) :
    let pm := model hp root Vmax hVmax source hsource hsourceF
    let packet := hp.frozenPacket root
    let ν := d.ν k (p.γ root)
    let μ := packet.selectedLaw ν S
    let code := clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) graphMesh
    let nativeRow := row ∘ (code ∘ p.childClockPoint root)
    let lab := p.childClockLabel root level (p.γ root)
    letI : IsProbabilityMeasure ν := (hd.weights k).2.2 _
    letI : IsProbabilityMeasure (pm.prior ν) := model_prior_probability hp root hVmax source hsource hsourceF hd
    letI : IsFiniteMeasure μ := (packet.selectedLaw_time_kernel ν
      (hp.assignment_mass_pos (by linarith [hd.1 k]) root).ne' hS (hSsource.trans hsourceF)).1
    ∀ input : RootPreparationInput pm ν μ (packet.selectedEvent S) row nativeRow lab,
    input.b=graphMesh →
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      let Src := S∩code ⁻¹' U
      let bad := {w | ¬Jets2.NativeGridQualified (p.childClockReference root level Src) lab nativeRow
        input.incidence.M input.T input.mesh input.bound input.err input.duration (packet.timeChange w)}
      MeasurableSet Src ∧
      (ν.prod volume) S  ≤  input.regularityFactor*(ν.prod volume) Src+
        (input.regularityFactor*input.supportLoss)*(ENNReal.ofReal packet.unitFrame.q*ν (p.A root)) ∧
      (∀ x∈Src, ∀ y∈Src, ‖row (code x)-row (code y)‖  ≤ 
        input.Lp*(‖clockParentCoordinates p root (SignalGraph.ancestorSignal (d.N k) p root) x-
          clockParentCoordinates p root (SignalGraph.ancestorSignal (d.N k) p root) y‖+input.ρ)) ∧
      MeasurableSet bad ∧
      ((ν.prod volume).restrict Src) bad  ≤ 
        input.incidence.nativeFailureBound*(ENNReal.ofReal packet.unitFrame.q*ν (p.A root)) := by
  dsimp only
  intro input hmeshEq
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let packet := hp.frozenPacket root
  let ν := d.ν k (p.γ root)
  let μ := packet.selectedLaw ν S
  let Eclock := packet.selectedEvent S
  let code := clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) graphMesh
  let nativeRow := row ∘ (code ∘ p.childClockPoint root)
  let lab := p.childClockLabel root level (p.γ root)
  letI : IsProbabilityMeasure ν := (hd.weights k).2.2 _
  letI : IsProbabilityMeasure (pm.prior ν) := model_prior_probability hp root hVmax source hsource hsourceF hd
  have hA : ν (p.A root)≠0 := (hp.assignment_mass_pos (by linarith [hd.1 k]) root).ne'
  have hSF : S⊆packet.counted := hSsource.trans hsourceF
  letI : IsFiniteMeasure μ := (packet.selectedLaw_time_kernel ν hA hS hSF).1
  let originalPart (A : Set Ev) := S∩packet.timeChange ⁻¹' A
  let reference (A : Set Ev) := p.childClockReference root level (originalPart A)
  have hpoint (z : Ev) : p.childClockPoint root z=packet.timeChange.symm z :=
    congrFun (hp.childClockPoint_eq_timeChange_symm root) z
  have hrefMeas : ∀ A, MeasurableSet A → A⊆Eclock → MeasurableSet (reference A) := by
    intro A hA _
    exact p.childClockReference_measurable root level (hS.inter (hA.preimage packet.timeChange.measurable))
  have hsourceRef : ∀ A, A⊆Eclock → A⊆reference A := by
    intro A hAE z hz
    obtain ⟨w,hw,hzEq⟩ := hAE hz
    subst z
    change p.childClockPoint root (packet.timeChange w)∈p.childReference root level (originalPart A)
    rw [hpoint,MeasurableEquiv.symm_apply_apply]
    exact ⟨⟨⟨hw,hz⟩,(hend w hw).1⟩,(hend w hw).2⟩
  have hrefTime : ∀ A, A⊆Eclock → ∀ z∈reference A, z.2∈Icc (0:ℝ) 1 := by
    intro A _ z hz
    have hw : p.childClockPoint root z∈S := hz.1.1.1
    have hzE : z∈Eclock := by
      refine ⟨p.childClockPoint root z,hw,?_⟩
      rw [hpoint]
      exact MeasurableEquiv.apply_symm_apply _ z
    exact pm.event_time z (image_mono hSsource hzE)
  obtain ⟨U,hU,hkeep,hmass,hLip,hbad,hfailure⟩ := input.run reference hrefMeas hsourceRef hrefTime
  let keepClock := Eclock∩(pm.physicalState input.b) ⁻¹' U
  let Src := S∩code ⁻¹' U
  change MeasurableSet keepClock at hkeep
  change MeasurableSet {z | ¬Jets2.NativeGridQualified (reference keepClock) lab nativeRow
    input.incidence.M input.T input.mesh input.bound input.err input.duration z} at hbad
  change ((pm.prior ν).prod volume) (keepClock\{z | Jets2.NativeGridQualified (reference keepClock) lab nativeRow
    input.incidence.M input.T input.mesh input.bound input.err input.duration z}) ≤ input.incidence.nativeFailureBound at hfailure
  have hSrc : MeasurableSet Src := hS.inter
    ((measurable_clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) graphMesh) hU)
  have hSrcS : Src⊆S := inter_subset_left
  have hclockState (x : Ev) (hx : x∈S) : pm.physicalState input.b (packet.timeChange x)=code x := by
    rw [hmeshEq]
    exact model_physicalState hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx) graphMesh
  have hselected : packet.selectedEvent Src=keepClock := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨⟨w,hw.1,rfl⟩,?_⟩
      change pm.physicalState input.b (packet.timeChange w)∈U
      rw [hclockState w hw.1]
      exact hw.2
    · rintro ⟨⟨w,hw,rfl⟩,hwU⟩
      refine ⟨w,⟨hw,?_⟩,rfl⟩
      change pm.physicalState input.b (packet.timeChange w)∈U at hwU
      rwa [hclockState w hw] at hwU
  have hpart : originalPart keepClock=Src := by
    ext w
    constructor
    · rintro ⟨hw,hwClock⟩
      refine ⟨hw,?_⟩
      have hh : pm.physicalState input.b (packet.timeChange w)∈U := hwClock.2
      rwa [hclockState w hw] at hh
    · intro hw
      exact ⟨hw.1,⟨⟨w,hw.1,rfl⟩,by
        change pm.physicalState input.b (packet.timeChange w)∈U
        rw [hclockState w hw.1]
        exact hw.2⟩⟩
  have hunitMass : μ keepClock=packet.selectedLaw ν Src univ := by
    change (((packet.prior ν).prod volume).restrict Eclock) keepClock=
      (((packet.prior ν).prod volume).restrict (packet.selectedEvent Src)) univ
    rw [Measure.restrict_apply hkeep,Measure.restrict_apply_univ,hselected,
      inter_eq_left.mpr (show keepClock⊆Eclock from inter_subset_left)]
  have hunitScaled : packet.selectedLaw ν S univ ≤ input.regularityFactor*packet.selectedLaw ν Src univ+
      input.regularityFactor*input.supportLoss := by
    rw [←hunitMass]
    simpa only [RootPreparationInput.regularityFactor,RootPreparationInput.supportLoss,
      mul_add,add_assoc] using hmass
  have horiginalMass := original_scaled_mass_bound_of_selected_mass_bound packet ν hA
    S Src hS hSrc hSF hSrcS input.regularityFactor (input.regularityFactor*input.supportLoss) hunitScaled
  let goodClock := {z | Jets2.NativeGridQualified (p.childClockReference root level Src) lab nativeRow
    input.incidence.M input.T input.mesh input.bound input.err input.duration z}
  have hbadClock : MeasurableSet goodClockᶜ := by
    change MeasurableSet {z | ¬Jets2.NativeGridQualified (p.childClockReference root level Src) lab nativeRow
      input.incidence.M input.T input.mesh input.bound input.err input.duration z}
    simpa only [reference,hpart] using hbad
  have hfailureClock : packet.selectedLaw ν Src goodClockᶜ ≤ input.incidence.nativeFailureBound := by
    rw [ParentSource.Broad.Source.FrozenPacket.selectedLaw,Measure.restrict_apply hbadClock,hselected]
    rw [←model_prior hp root hVmax source hsource hsourceF ν]
    convert hfailure using 1
    congr 1
    ext z
    simp only [reference,hpart,goodClock,mem_inter_iff,mem_compl_iff,mem_sdiff,mem_ofPred_eq]
    tauto
  have horiginalFail := original_event_bound_of_selected_bound packet ν hA Src hSrc
    (hSrcS.trans hSF) goodClockᶜ hbadClock input.incidence.nativeFailureBound hfailureClock
  refine ⟨U,hU,hSrc,horiginalMass,?_,?_,horiginalFail⟩
  · intro x hx y hy
    have hxClock : packet.timeChange x∈keepClock := by
      rw [←hselected]
      exact ⟨x,hx,rfl⟩
    have hyClock : packet.timeChange y∈keepClock := by
      rw [←hselected]
      exact ⟨y,hy,rfl⟩
    have hh := hLip (packet.timeChange x) hxClock (packet.timeChange y) hyClock
    rw [hclockState x hx.1,hclockState y hy.1,
      model_originalPoint hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx.1),
      model_originalPoint hp root hVmax source hsource hsourceF hR hvelocity (hSsource hy.1)] at hh
    exact hh
  · exact hbadClock.preimage packet.timeChange.measurable

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestor
