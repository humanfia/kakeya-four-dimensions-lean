-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorRecordChildLocalization, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RecordNaturalStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAncestorHistories

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open scoped ENNReal

noncomputable section

/-- A whole-record restriction keeps the original reference floor,
including the option that the record has zero current mass. -/
theorem record_floor_restrict_of_whole
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (piece region : Set Ω) (hregion : MeasurableSet region)
    (hwhole : (piece∩region).Nonempty → piece⊆region)
    (weight : ENNReal) (hfloor : μ piece=0 ∨ weight ≤ μ piece) :
    (μ.restrict region) piece=0 ∨ weight ≤ (μ.restrict region) piece := by
  by_cases h : (piece∩region).Nonempty
  · simpa only [Measure.restrict_eq_self μ (hwhole h)] using hfloor
  · left
    rw [Measure.restrict_apply' hregion,Set.not_nonempty_iff_eq_empty.mp h,measure_empty]

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Choosing a later child costs no record-floor or ratio loss. Actual
original ancestry makes every source record meeting that child wholly
contained in it. The identical records can therefore renew states at a
loss charged to the CHILD reservoir rather than the full ancestor. -/
theorem Native.PaletteFamily.record_child_localization
    {Rec : Type*} (root child : Fin p.C)
    (hworld : p.γ child=p.γ root) (hchild : p.lev child ≤ stop)
    (fine : Rec → ↥(F.retainedOriginalFinePackets root))
    (piece : Rec → Set Ev)
    (hsub : ∀ rec, piece rec⊆F.fineOriginalEvent root (fine rec).1 univ)
    (hbase : ∀ rec, piece rec⊆Q.base (p.γ root)) :
    (∀ rec, (piece rec∩p.F child).Nonempty → piece rec⊆p.F child) ∧
    ∀ (μ : Measure Ev) (weight : Rec → ENNReal),
      (∀ rec, μ (piece rec)=0 ∨ weight rec ≤ μ (piece rec)) →
      (∀ rec, (μ.restrict (p.F child)) (piece rec)=0 ∨
        weight rec ≤ (μ.restrict (p.F child)) (piece rec)) ∧
      ∀ (B : Set Ev) (cap : ENNReal),
        (∀ rec, μ (piece rec∩B) ≤ cap*μ (piece rec)) →
        ∀ rec, (μ.restrict (p.F child)) (piece rec∩B) ≤
          cap*(μ.restrict (p.F child)) (piece rec) := by
  classical
  have hwhole (rec : Rec) (hne : (piece rec∩p.F child).Nonempty) : piece rec⊆p.F child := by
    obtain ⟨z,hz,hzc⟩ := hne
    have hspec := (Finset.mem_filter.mp (F.retained_original_fine_spec root (fine rec)).1).2
    have hh := F.fine_original_event_whole_earlier_packet hp root (fine rec).1 child
      hspec.1 hspec.2.1 hworld hchild z (hsub rec hz) (hbase rec hz) hzc
    exact fun _ hw => hh (hsub rec hw)
  have hm : MeasurableSet (p.F child) :=
    (hp.2.2.2.2.2.2.2 child).2.2.2.2.2.2.2.2.2.1
  refine ⟨hwhole,?_⟩
  intro μ weight hfloor
  refine ⟨fun rec => record_floor_restrict_of_whole μ (piece rec) (p.F child) hm
    (hwhole rec) (weight rec) (hfloor rec),?_⟩
  intro B cap hcap rec
  exact record_ratio_restrict_of_whole μ (piece rec) (p.F child) B hm (hwhole rec) cap (hcap rec)

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
