-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.SignalModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Generalizes, from the physical parent `d.P` to an arbitrary signal polynomial `X`, the clock
-- model of this obligation's port of o287 (Parent/Graph/ClockStageRows.lean, session x1037 of
-- o287, with x1046's clock stages of o265); written by x1082 for the relative row packet.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.ClockStageRows

/-!
# The clock model of an arbitrary signal

`Parent/Graph/ClockStageRows.lean` builds the physical velocity model of an old packet for the
physical parent `P` of the problem: the literal clock coefficients of `P` (signal `2^T P`,
unsheared old base, original velocity) on the lines where `P` has bounded jets. The relative
row packet needs the same model for another signal: the test of an ancestor packet. Its jets are
bounded on the ancestor's assignment only (Markov on the ancestor's block), not on the whole unit
time, so the set of good lines is a parameter here.

* `safeSignalCoefficients X good`: the clock coefficients of `X` on `good`, jets erased elsewhere.
* `signalModel`: the `Qualification.PhysicalModel` over the time-changed events of a source `J`
  on good lines, with a coefficient bound `B` (the constant `2^T X` may be large: only the jets
  enter the rows).
* `signalModel_code_eq`, `signalModel_planar`, `signalModel_assignedCode`: the model reads the
  clock code of `X` (`clockParentCode p old X`), the original planar velocity and the assigned
  clock code, exactly as for `P`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native ParentSource.Broad.Source
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open scoped ENNReal

noncomputable section

/-- The clock coefficients of a signal `X` on the good lines, with the four jets erased off them. -/
def safeSignalCoefficients {W : ℕ} (X : Po) (good : Set Ln) (p : PathData W) (old : Fin p.C)
    (l : Ln) : Fin 7 → ℝ := by
  classical
  exact if l ∈ good then ParentSignal.clockPacketCoefficients X p old l else
    ParentSignal.eraseClockJets (ParentSignal.clockPacketCoefficients X p old l)

theorem safeSignalCoefficients_eq {W : ℕ} (X : Po) (good : Set Ln) (p : PathData W)
    (old : Fin p.C) {l : Ln} (hl : l ∈ good) :
    safeSignalCoefficients X good p old l = ParentSignal.clockPacketCoefficients X p old l := by
  classical
  exact ite_eq_left hl

theorem measurable_safeSignalCoefficients {W : ℕ} (X : Po) {good : Set Ln}
    (hgood : MeasurableSet good) (p : PathData W) (old : Fin p.C) :
    Measurable (safeSignalCoefficients X good p old) := by
  classical
  have hc := ParentSignal.measurable_clockPacketCoefficients X p old
  exact Measurable.ite hgood hc (ParentSignal.measurable_eraseClockJets.comp hc)

/-- The jets of the safe coefficients are bounded everywhere once they are bounded on `good`. -/
theorem safeSignalCoefficients_jets {W : ℕ} (X : Po) (good : Set Ln) (p : PathData W)
    (old : Fin p.C) {H : ℝ} (hH : 0 ≤ H)
    (hjets : ∀ l ∈ good, |ParentSignal.clockPacketCoefficients X p old l 1| ≤ H ∧
      |ParentSignal.clockPacketCoefficients X p old l 2| ≤ H ∧
      |ParentSignal.clockPacketCoefficients X p old l 4| ≤ H ∧
      |ParentSignal.clockPacketCoefficients X p old l 6| ≤ H) (l : Ln) :
    |safeSignalCoefficients X good p old l 1| ≤ H ∧
      |safeSignalCoefficients X good p old l 2| ≤ H ∧
      |safeSignalCoefficients X good p old l 4| ≤ H ∧
      |safeSignalCoefficients X good p old l 6| ≤ H := by
  classical
  by_cases hl : l ∈ good
  · rw [safeSignalCoefficients_eq X good p old hl]
    exact hjets l hl
  · have h : safeSignalCoefficients X good p old l =
        ParentSignal.eraseClockJets (ParentSignal.clockPacketCoefficients X p old l) := ite_eq_right hl
    rw [h]
    simp [ParentSignal.eraseClockJets, hH]

section Model

variable {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (old : Fin p.C) (X : Po) (good : Set Ln)

/-- The events of the signal model over an original source `J`. -/
def signalEvent (J : Set Ev) : Set Ev :=
  (hp.frozenPacket old).selectedEvent (J ∩ Prod.fst ⁻¹' good)

theorem measurable_signalEvent (hgood : MeasurableSet good) {J : Set Ev} (hJ : MeasurableSet J) :
    MeasurableSet (signalEvent hp old good J) :=
  (hp.frozenPacket old).measurable_selectedEvent (hJ.inter (measurable_fst hgood))

theorem signalEvent_assignment {J : Set Ev} (hJF : J ⊆ p.F old) :
    ∀ z ∈ signalEvent hp old good J, z.1 ∈ (hp.frozenPacket old).assigned := by
  rintro z ⟨x, ⟨hxJ, -⟩, rfl⟩
  rw [clock_timeChange hp old x]
  exact ((hp.frozenPacket old).counted_inside_original (hJF hxJ)).2.1

theorem signalEvent_time {J : Set Ev} (hJF : J ⊆ p.F old) :
    ∀ z ∈ signalEvent hp old good J, z.2 ∈ Icc (0 : ℝ) 1 := by
  intro z hz
  exact ((hp.frozenPacket old).event_unit_time
    ((hp.frozenPacket old).selectedEvent_subset (inter_subset_left.trans hJF) hz)).2

variable {B : ℝ}

theorem signalEvent_coefficients
    (hcoef : ∀ l ∈ good, l ∈ p.A old → ∀ i, |ParentSignal.clockPacketCoefficients X p old l i| ≤ B)
    {J : Set Ev} (hJF : J ⊆ p.F old) :
    ∀ z ∈ signalEvent hp old good J, ∀ i, |safeSignalCoefficients X good p old z.1 i| ≤ B := by
  rintro z ⟨x, ⟨hxJ, hxG⟩, rfl⟩ i
  rw [clock_timeChange hp old x]
  change |safeSignalCoefficients X good p old x.1 i| ≤ B
  rw [safeSignalCoefficients_eq X good p old hxG]
  exact hcoef x.1 hxG ((hp.frozenPacket old).counted_inside_original (hJF hxJ)).2.1 i

/-- **The clock model of a signal** over a measurable original source `J` of the old packet:
the clock coefficients of `X` (signal `2^T X`, unsheared old base, original planar velocity)
with jets erased off `good`, its assignment the full old assignment cut to the coefficient
bound `B`, and its events the time-changed incidences of `J` on good lines. -/
def signalModel (hgood : MeasurableSet good) (hB : 0 ≤ B)
    (hcoef : ∀ l ∈ good, l ∈ p.A old → ∀ i, |ParentSignal.clockPacketCoefficients X p old l i| ≤ B)
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) :
    Qualification.PhysicalModel :=
  Qualification.PhysicalModel.ofCoefficients (safeSignalCoefficients X good p old)
    (measurable_safeSignalCoefficients X hgood p old)
    (hp.frozenPacket old).assigned (hp.frozenPacket old).measurable_assigned
    B hB (signalEvent hp old good J) (measurable_signalEvent hp old good hgood hJ)
    (signalEvent_assignment hp old good hJF) (signalEvent_time hp old good hJF)
    (signalEvent_coefficients hp old X good hcoef hJF)

variable (hgood : MeasurableSet good) (hB : 0 ≤ B)
    (hcoef : ∀ l ∈ good, l ∈ p.A old → ∀ i, |ParentSignal.clockPacketCoefficients X p old l i| ≤ B)

theorem signalModel_event (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) :
    (signalModel hp old X good hgood hB hcoef J hJ hJF).event = signalEvent hp old good J := rfl

theorem signalModel_coefficients (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) :
    (signalModel hp old X good hgood hB hcoef J hJ hJF).scalarCoefficients =
      safeSignalCoefficients X good p old := rfl

/-- A good assigned line is assigned in the signal model. -/
theorem signalModel_assigned (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) {l : Ln}
    (hl : l ∈ p.A old) (hG : l ∈ good) :
    l ∈ (signalModel hp old X good hgood hB hcoef J hJ hJF).assigned := by
  refine ⟨hl, fun i => ?_⟩
  rw [safeSignalCoefficients_eq X good p old hG]
  exact hcoef l hG hl i

/-- The jets of the signal model on its assigned lines. -/
theorem signalModel_jets (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) {H : ℝ}
    (hH : 0 ≤ H)
    (hjets : ∀ l ∈ good, |ParentSignal.clockPacketCoefficients X p old l 1| ≤ H ∧
      |ParentSignal.clockPacketCoefficients X p old l 2| ≤ H ∧
      |ParentSignal.clockPacketCoefficients X p old l 4| ≤ H ∧
      |ParentSignal.clockPacketCoefficients X p old l 6| ≤ H) :
    ∀ l ∈ (signalModel hp old X good hgood hB hcoef J hJ hJF).assigned,
      |(signalModel hp old X good hgood hB hcoef J hJ hJF).scalarCoefficients l 1| ≤ H ∧
      |(signalModel hp old X good hgood hB hcoef J hJ hJF).scalarCoefficients l 2| ≤ H ∧
      |(signalModel hp old X good hgood hB hcoef J hJ hJF).scalarCoefficients l 4| ≤ H ∧
      |(signalModel hp old X good hgood hB hcoef J hJ hJF).scalarCoefficients l 6| ≤ H :=
  fun l _ => safeSignalCoefficients_jets X good p old hH hjets l

/-- On a good counted incidence the model code of the time-changed incidence reads the clock
coordinates of `X`: the unsheared base and `X` in clock units. -/
theorem signalModel_code (hX : X.totalDegree ≤ 2) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {x : Ev} (hxF : x ∈ p.F old) (hG : x.1 ∈ good) (b h : ℝ) :
    modelCode (signalModel hp old X good hgood hB hcoef J hJ hJF) b h
        ((hp.frozenPacket old).timeChange x) =
      fun j => ⌊clockParentCoordinates p old X x j / (if j = 3 then h else b)⌋ := by
  have hA : x.1 ∈ p.A old := ((hp.frozenPacket old).counted_inside_original hxF).2.1
  have hl := signalModel_assigned hp old X good hgood hB hcoef J hJ hJF hA hG
  have hpt := ParentSignal.clockPacket_point hX p old x
  rw [← safeSignalCoefficients_eq X good p old hG] at hpt
  rw [clock_timeChange hp old x]
  funext j
  simp only [modelCode, coefficientGridCode]
  rw [modelCoefficients_of_mem _ hl, signalModel_coefficients]
  change ⌊coefficientPhysical (safeSignalCoefficients X good p old x.1) (packetTime p old x) j /
    _⌋ = _
  rw [hpt]
  congr 2
  fin_cases j <;> rfl

/-- At equal base and signal mesh the model code is the clock code of `X`. -/
theorem signalModel_code_eq (hX : X.totalDegree ≤ 2) (J : Set Ev) (hJ : MeasurableSet J)
    (hJF : J ⊆ p.F old) {x : Ev} (hxF : x ∈ p.F old) (hG : x.1 ∈ good) (b : ℝ) :
    modelCode (signalModel hp old X good hgood hB hcoef J hJ hJF) b b
        ((hp.frozenPacket old).timeChange x) = clockParentCode p old X b x := by
  rw [signalModel_code hp old X good hgood hB hcoef hX J hJ hJF hxF hG b b]
  funext j
  simp only [ite_self]
  rfl

/-- On a good line the planar velocity of the model is the original one. -/
theorem signalModel_planar (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old) {l : Ln}
    (hG : l ∈ good) :
    modelPlanar (signalModel hp old X good hgood hB hcoef J hJ hJF) l = v l := by
  have hv := ParentSignal.clockPacket_velocity X p old l
  rw [← safeSignalCoefficients_eq X good p old hG] at hv
  ext i
  fin_cases i
  · exact congrFun hv 0
  · exact congrFun hv 1

/-- The assigned clock code of `X` and the model code agree at every time of a good assigned
line. -/
theorem signalModel_assignedCode (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old)
    {l : Ln} (hl : l ∈ (hp.frozenPacket old).assigned) (hG : l ∈ good) (b t : ℝ) :
    hp.assignedClockCode old X b (⟨l, hl⟩, t) =
      modelCode (signalModel hp old X good hgood hB hcoef J hJ hJF) b b (l, t) := by
  have hlm := signalModel_assigned hp old X good hgood hB hcoef J hJ hJF hl hG
  funext j
  simp only [Native.PathData.Valid.assignedClockCode, curveCoarseCode,
    Native.PathData.Valid.assignedClockCurve, Native.PathData.Valid.assignedClockCoefficients,
    modelCode, coefficientGridCode, ite_self]
  rw [modelCoefficients_of_mem _ hlm, signalModel_coefficients]
  change _ = ⌊coefficientPhysical (safeSignalCoefficients X good p old l) t j / b⌋
  rw [safeSignalCoefficients_eq X good p old hG]
  congr 2

end Model

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph
