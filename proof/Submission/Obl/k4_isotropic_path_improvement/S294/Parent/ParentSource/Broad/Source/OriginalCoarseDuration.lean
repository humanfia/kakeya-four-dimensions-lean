-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalCoarseDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalCoarseDuration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalCoarseDuration.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalNativeCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CoarseDuration

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Broad.Velocity
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

def Native.PathData.Valid.assignedCoarseCode (old : Fin p.C) (coarse : ℝ) :
    (hp.frozenPacket old).AssignedLine × ℝ → Fin 4 → ℤ :=
  nativeCoarseCode (normalizedPacketTest Nk p old)
    (fun l => normalizedPacketPosition p old l) (fun l => normalizedPacketVelocity p old l) coarse

def Native.PathData.Valid.assignedCoarseCellSource (old : Fin p.C) (J : Set Ev)
    (coarse : ℝ) (q : Fin 4 → ℤ) : Set ((hp.frozenPacket old).AssignedLine × ℝ) :=
  (hp.frozenPacket old).assignedSelectedEvent J ∩ hp.assignedCoarseCode old coarse ⁻¹' {q}

include hp

theorem Native.PathData.Valid.assignedCoarseCode_eq_original (old : Fin p.C) (coarse : ℝ)
    (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    hp.assignedCoarseCode old coarse z =
      p.originalPhysicalCode Nk old coarse coarse ((hp.frozenPacket old).originalIncidence z) := by
  rw [hp.assigned_physical_code]
  simp only [assignedCoarseCode, ite_self]
  rfl

theorem Native.PathData.Valid.measurable_assignedCoarseCode (old : Fin p.C) (coarse : ℝ) :
    Measurable (hp.assignedCoarseCode old coarse) := by
  have hh := (p.measurable_originalPhysicalCode Nk old coarse coarse).comp
    (hp.frozenPacket old).measurable_originalIncidence
  convert hh using 1
  funext z
  exact hp.assignedCoarseCode_eq_original old coarse z

/-- The actual earlier coarse-cell duration bounds its original retained
trajectory prior in the real units used by the Kakeya moment. -/
theorem Native.PathData.Valid.original_coarse_duration_prior_cap
    (hN : 0 < Nk) (old : Fin p.C) [IsFiniteMeasure (ν (p.γ old))]
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old)
    {coarse lossRate : ℝ} (hcoarse : 0 < coarse) (hRate : 0 < lossRate) (q : Fin 4 → ℤ) :
    (((hp.frozenPacket old).assignedPrior (ν (p.γ old))).restrict
      {l | ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (hp.assignedCoarseCellSource old J coarse q) l}).real univ ≤
      ((hp.frozenPacket old).assignedSelectedLaw (ν (p.γ old)) J).real
        (hp.assignedCoarseCode old coarse ⁻¹' {q}) / (lossRate * coarse) := by
  let packet := hp.frozenPacket old
  let prior := packet.assignedPrior (ν (p.γ old))
  have hA : ν (p.γ old) packet.assigned ≠ 0 := (hp.assignment_mass_pos hN old).ne'
  letI : IsProbabilityMeasure prior := packet.assignedPrior_probability (ν (p.γ old)) hA
  let source := hp.assignedCoarseCellSource old J coarse q
  have hcell : MeasurableSet (hp.assignedCoarseCode old coarse ⁻¹' {q}) :=
    (hp.measurable_assignedCoarseCode old coarse) (measurableSet_singleton q)
  have hsource : MeasurableSet source := (packet.measurable_assignedSelectedEvent hJ).inter hcell
  let a := ENNReal.ofReal (lossRate * coarse)
  let long := {l | a ≤ incidenceDuration source l}
  have hlong : MeasurableSet long :=
    measurableSet_le measurable_const (measurable_incidenceDuration hsource)
  have hh := retained_duration_prior_bound prior hsource MeasurableSet.univ hlong a
    (fun l hl => hl.2)
  rw [Measure.restrict_apply_univ, duration_withDensity_apply prior hsource MeasurableSet.univ] at hh
  simp only [univ_prod, preimage_univ, inter_univ] at hh
  let μ := packet.assignedSelectedLaw (ν (p.γ old)) J
  letI : IsFiniteMeasure μ := packet.assignedSelectedLaw_finite (ν (p.γ old)) hA hJ hJF
  have hmass : (prior.prod volume) source = μ (hp.assignedCoarseCode old coarse ⁻¹' {q}) := by
    change (prior.prod volume) source =
      ((prior.prod volume).restrict (packet.assignedSelectedEvent J))
        (hp.assignedCoarseCode old coarse ⁻¹' {q})
    rw [Measure.restrict_apply hcell]
    exact congrArg ((prior.prod volume) : Set _ → ENNReal) (inter_comm _ _)
  rw [hmass] at hh
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hh
  simp only [measureReal_def, Measure.restrict_apply_univ]
  change (prior long).toReal ≤ (μ (hp.assignedCoarseCode old coarse ⁻¹' {q})).toReal /
    (lossRate * coarse)
  apply (le_div_iff₀ (mul_pos hRate hcoarse)).mpr
  have hreal' : (lossRate * coarse) * (prior long).toReal ≤
      (μ (hp.assignedCoarseCode old coarse ⁻¹' {q})).toReal := by
    simpa only [a, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_pos hRate hcoarse).le] using hreal
  nlinarith only [hreal']

/-- A concrete original packet source supplies the coarse-cell duration
cut and prior caps. All deletion costs use the FULL old reference; all
duration witnesses belong to the EARLIER original source. -/
theorem Native.PathData.Valid.prune_original_coarse_durations
    (hN : 0 < Nk) (old : Fin p.C) [IsFiniteMeasure (ν (p.γ old))]
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old)
    {coarse lossRate : ℝ} (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1)
    (hRate : 0 ≤ lossRate) :
    ∃ J' : Set Ev, MeasurableSet J' ∧ J' ⊆ J ∧
      (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹) * ν (p.γ old) (p.A old))⁻¹ *
          ((ν (p.γ old)).prod volume) (J \ J') ≤
        ENNReal.ofReal (5 * lossRate * (114 * (3 * p.κ) + 5) ^ 4) ∧
      (∀ z ∈ (hp.frozenPacket old).assignedSelectedEvent J',
        ENNReal.ofReal (lossRate * coarse) ≤
          incidenceDuration (hp.assignedCoarseCellSource old J coarse
            (hp.assignedCoarseCode old coarse z)) z.1) ∧
      ∀ q : Fin 4 → ℤ,
        ENNReal.ofReal (lossRate * coarse) *
            (hp.frozenPacket old).assignedPrior (ν (p.γ old))
              {l | ENNReal.ofReal (lossRate * coarse) ≤
                incidenceDuration (hp.assignedCoarseCellSource old J coarse q) l} ≤
          (((hp.frozenPacket old).assignedPrior (ν (p.γ old))).prod volume)
            (hp.assignedCoarseCellSource old J coarse q) := by
  let packet := hp.frozenPacket old
  have hA : ν (p.γ old) packet.assigned ≠ 0 := (hp.assignment_mass_pos hN old).ne'
  letI : IsProbabilityMeasure (packet.assignedPrior (ν (p.γ old))) :=
    packet.assignedPrior_probability (ν (p.γ old)) hA
  obtain ⟨keep, hkeep, hkeepE, hloss, hlong, hprior⟩ := exists_native_coarse_duration_source
    (packet.assignedPrior (ν (p.γ old))) (normalizedPacketTest Nk p old)
    (normalizedPacketTest_degree hp old)
    (fun l => normalizedPacketPosition p old l) (fun l => normalizedPacketVelocity p old l)
    (by linarith [hp.1] : 0 ≤ 3 * p.κ) hcoarse hcoarse1 hRate
    (hp.assigned_base_velocity_bound old)
    (fun l t ht => (hp.assigned_whole_native_curve old l t ht).trans (by linarith [hp.1]))
    (hp.measurable_assigned_physical_curve old)
    (packet.assignedSelectedEvent J) (packet.measurable_assignedSelectedEvent hJ)
    (packet.assignedSelectedEvent_unit_time hJF)
  let J' := packet.originalCut J keep
  refine ⟨J', packet.measurable_originalCut hJ hkeep, packet.originalCut_subset J keep, ?_, ?_, hprior⟩
  · change (ENNReal.ofReal packet.unitFrame.q * ν (p.γ old) packet.assigned)⁻¹ *
      ((ν (p.γ old)).prod volume) (J \ packet.originalCut J keep) ≤ _
    rw [← packet.originalCut_loss (ν (p.γ old)) hA hJ hJF hkeep,
      Broad.Source.FrozenPacket.assignedSelectedLaw, Measure.restrict_apply hkeep.compl]
    simpa only [measure_univ, mul_one, sdiff_eq, inter_comm] using hloss
  · intro z hz
    rw [packet.assignedSelectedEvent_originalCut] at hz
    exact hlong z hz.2

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
