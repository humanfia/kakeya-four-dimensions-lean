-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ClockCurveDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ClockCurveDuration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ClockCurveDuration.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.LipschitzCoarseDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentCoefficients
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalScalarCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentClockState
import Submission.Lib.K4PolynomialNorming.AffineLineSimulation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Broad.Source Broad.Velocity
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

noncomputable section

/-- Only the varying coefficients control the number of spatial cells
visited by a quadratic trajectory. Constant offsets are unrestricted. -/
theorem scalarPhysicalPoint_lipschitz_of_nonconstant_bound {c : Fin 7 → ℝ} {H : ℝ}
    (hH : 1 ≤ H) (hc : ∀ e : Fin 7, e ≠ 0 → |c e| ≤ H)
    {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (j : Fin 4) :
    |scalarPhysicalPoint c s j-scalarPhysicalPoint c t j| ≤ 3*H*|s-t| := by
  fin_cases j
  · change |s-t| ≤ 3*H*|s-t|
    nlinarith only [abs_nonneg (s-t),hH]
  · change |c 3+c 4*s-(c 3+c 4*t)| ≤ _
    rw [show c 3+c 4*s-(c 3+c 4*t) = c 4*(s-t) by ring,abs_mul]
    calc
      _ ≤ H*|s-t| := mul_le_mul_of_nonneg_right (hc 4 (by decide)) (abs_nonneg _)
      _ ≤ _ := by nlinarith only [abs_nonneg (s-t),hH]
  · change |c 5+c 6*s-(c 5+c 6*t)| ≤ _
    rw [show c 5+c 6*s-(c 5+c 6*t) = c 6*(s-t) by ring,abs_mul]
    calc
      _ ≤ H*|s-t| := mul_le_mul_of_nonneg_right (hc 6 (by decide)) (abs_nonneg _)
      _ ≤ _ := by nlinarith only [abs_nonneg (s-t),hH]
  · change |Jets2.zx c s-Jets2.zx c t| ≤ _
    have heq (u : ℝ) : Jets2.zx c u =
        Submission.Lib.K4PolynomialNorming.quadraticHeight (c 0) (c 1) (c 2) u := by
      dsimp [Jets2.zx,Submission.Lib.K4PolynomialNorming.quadraticHeight]
      ring
    rw [heq,heq]
    calc
      _ ≤ |s-t| * (|c 1|+2*|c 2|) :=
        Submission.Lib.K4PolynomialNorming.quadratic_height_time_difference_le _ _ _ _ _ hs ht
      _ ≤ |s-t| * (H+2*H) := by
        gcongr
        · exact hc 1 (by decide)
        · exact hc 2 (by decide)
      _ = _ := by ring

theorem measurable_scalarPhysicalPoint {X : Type*} [MeasurableSpace X]
    (c : X → Fin 7 → ℝ) (hc : Measurable c) :
    Measurable (fun z : X × ℝ => scalarPhysicalPoint (c z.1) z.2) := by
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j
  all_goals dsimp [scalarPhysicalPoint,Jets2.zy,Jets2.zx]
  all_goals fun_prop

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

def Native.PathData.Valid.assignedClockCoefficients (old : Fin p.C) (P : Po)
    (l : (hp.frozenPacket old).AssignedLine) : Fin 7 → ℝ :=
  ParentSignal.clockPacketCoefficients P p old l

def Native.PathData.Valid.assignedClockCurve (old : Fin p.C) (P : Po)
    (l : (hp.frozenPacket old).AssignedLine) (t : ℝ) : Fin 4 → ℝ :=
  scalarPhysicalPoint (hp.assignedClockCoefficients old P l) t

def Native.PathData.Valid.assignedClockCode (old : Fin p.C) (P : Po) (coarse : ℝ) :
    (hp.frozenPacket old).AssignedLine × ℝ → Fin 4 → ℤ :=
  curveCoarseCode (hp.assignedClockCurve old P) coarse

def Native.PathData.Valid.assignedClockCellSource (old : Fin p.C) (P : Po)
    (J : Set Ev) (coarse : ℝ) (q : Fin 4 → ℤ) :
    Set ((hp.frozenPacket old).AssignedLine × ℝ) :=
  (hp.frozenPacket old).assignedSelectedEvent J ∩ hp.assignedClockCode old P coarse ⁻¹' {q}

include hp

theorem Native.PathData.Valid.measurable_assignedClockCoefficients (old : Fin p.C) (P : Po) :
    Measurable (hp.assignedClockCoefficients old P) :=
  (ParentSignal.measurable_clockPacketCoefficients P p old).comp measurable_subtype_coe

theorem Native.PathData.Valid.measurable_assignedClockCurve (old : Fin p.C) (P : Po) :
    Measurable (fun z : (hp.frozenPacket old).AssignedLine × ℝ =>
      hp.assignedClockCurve old P z.1 z.2) :=
  measurable_scalarPhysicalPoint _ (hp.measurable_assignedClockCoefficients old P)

theorem Native.PathData.Valid.measurable_assignedClockCode (old : Fin p.C) (P : Po)
    (coarse : ℝ) : Measurable (hp.assignedClockCode old P coarse) := by
  apply measurable_pi_iff.mpr
  intro j
  exact Int.measurable_floor.comp (((measurable_pi_apply j).comp
    (hp.measurable_assignedClockCurve old P)).div_const coarse)

/-- Exact physical clock coordinates on the original tagged incidence. -/
theorem Native.PathData.Valid.assignedClockCurve_eq_original (old : Fin p.C) {P : Po}
    (hP : P.totalDegree ≤ 2) (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    hp.assignedClockCurve old P z.1 z.2 =
      Fin.snoc (fun j => unshearedPacketBase p old
        ((hp.frozenPacket old).originalIncidence z) j)
        (clockParentSignal p old P ((hp.frozenPacket old).originalIncidence z)) := by
  let q := (hp.frozenPacket old).originalIncidence z
  have htime : packetTime p old q = z.2 := hp.originalIncidence_time old z
  have hline : q.1 = (z.1 : Ln) := (hp.frozenPacket old).originalIncidence_fst z
  have hb := ParentSignal.clockPacket_base P p old q
  have hx := ParentSignal.clockPacket_signal hP p old q
  rw [htime,hline] at hb hx
  have hb0 := congrArg (fun v : P2 => v 0) hb
  have hb1 := congrArg (fun v : P2 => v 1) hb
  ext j
  fin_cases j
  · change z.2 = unshearedPacketBase p old q 0
    exact htime.symm
  · exact hb0
  · exact hb1
  · exact hx

/-- The earlier original clock-cell mass controls the retained part of
the full original trajectory prior in the real units used by MK4. -/
theorem Native.PathData.Valid.original_clock_duration_prior_cap
    (hN : 0 < Nk) (old : Fin p.C) (P : Po) [IsFiniteMeasure (ν (p.γ old))]
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J⊆p.F old)
    {coarse lossRate : ℝ} (hcoarse : 0 < coarse) (hRate : 0 < lossRate) (q : Fin 4 → ℤ) :
    (((hp.frozenPacket old).assignedPrior (ν (p.γ old))).restrict
      {l | ENNReal.ofReal (lossRate*coarse) ≤
        incidenceDuration (hp.assignedClockCellSource old P J coarse q) l}).real univ ≤
      ((hp.frozenPacket old).assignedSelectedLaw (ν (p.γ old)) J).real
        (hp.assignedClockCode old P coarse ⁻¹' {q})/(lossRate*coarse) := by
  let packet := hp.frozenPacket old
  have hA : ν (p.γ old) packet.assigned ≠ 0 := (hp.assignment_mass_pos hN old).ne'
  letI : IsProbabilityMeasure (packet.assignedPrior (ν (p.γ old))) :=
    packet.assignedPrior_probability (ν (p.γ old)) hA
  exact earlier_cell_duration_prior_cap_real (packet.assignedPrior (ν (p.γ old)))
    (packet.assignedSelectedEvent J) (packet.measurable_assignedSelectedEvent hJ)
    (packet.assignedSelectedEvent_unit_time hJF) (hp.assignedClockCode old P coarse)
    (hp.measurable_assignedClockCode old P coarse) q (mul_pos hRate hcoarse)

end Path

section Problem

variable {d : Native.ProblemData} (hd : d.Valid) {k m : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Prune short earlier clock-cell durations on the original assignment.
The constant signal offset and the inverse old clock do not enter the loss. -/
theorem Native.PathData.Valid.prune_original_clock_durations
    (old : Fin p.C) {K coarse lossRate : ℝ} (hK : 24 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) [IsFiniteMeasure (d.ν k (p.γ old))]
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F old)
    (hgood : ∀ q∈J, q.1∈ParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)))
    (hvel : ∀ q∈J, ‖v q.1‖ ≤ d.K k)
    (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1) (hRate : 0 ≤ lossRate) :
    ∃ J' : Set Ev, MeasurableSet J' ∧ J' ⊆ J ∧
      (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹) * d.ν k (p.γ old) (p.A old))⁻¹ *
          ((d.ν k (p.γ old)).prod volume) (J \ J') ≤
        ENNReal.ofReal (lossRate*(3*K^4+3)*(7:ℝ)^4) ∧
      (∀ z∈(hp.frozenPacket old).assignedSelectedEvent J',
        ENNReal.ofReal (lossRate*coarse) ≤ incidenceDuration
          (hp.assignedClockCellSource old (d.P k (p.γ old)) J coarse
            (hp.assignedClockCode old (d.P k (p.γ old)) coarse z)) z.1) ∧
      ∀ q : Fin 4 → ℤ, ENNReal.ofReal (lossRate*coarse)*
        (hp.frozenPacket old).assignedPrior (d.ν k (p.γ old))
          {l | ENNReal.ofReal (lossRate*coarse) ≤ incidenceDuration
            (hp.assignedClockCellSource old (d.P k (p.γ old)) J coarse q) l} ≤
          (((hp.frozenPacket old).assignedPrior (d.ν k (p.γ old))).prod volume)
            (hp.assignedClockCellSource old (d.P k (p.γ old)) J coarse q) := by
  let packet := hp.frozenPacket old
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hA : d.ν k (p.γ old) packet.assigned ≠ 0 := (hp.assignment_mass_pos hN old).ne'
  letI : IsProbabilityMeasure (packet.assignedPrior (d.ν k (p.γ old))) :=
    packet.assignedPrior_probability (d.ν k (p.γ old)) hA
  have hLip : ∀ z∈packet.assignedSelectedEvent J, ∀ s∈Icc (0:ℝ) 1,
      ∀ t∈Icc (0:ℝ) 1, ∀ j,
      |hp.assignedClockCurve old (d.P k (p.γ old)) z.1 s j-
        hp.assignedClockCurve old (d.P k (p.γ old)) z.1 t j| ≤ 3*K^4*|s-t| := by
    intro z hz s hs t ht j
    have hq : packet.originalIncidence z∈J := by
      rwa [packet.assignedSelectedEvent_originalIncidence] at hz
    have hc := ParentSignal.clockPacket_nonconstant_coefficients_bound hd hp old hK hmax
      (hJF hq) (hgood _ hq) (hvel _ hq)
    rw [packet.originalIncidence_fst] at hc
    exact scalarPhysicalPoint_lipschitz_of_nonconstant_bound
      (by
        have hK1 : 1 ≤ K := by linarith
        exact one_le_pow₀ hK1) hc hs ht j
  obtain ⟨keep,hkeep,hkeepE,hloss,hlong,hprior⟩ := exists_lipschitz_coarse_duration_source
    (packet.assignedPrior (d.ν k (p.γ old)))
    (hp.assignedClockCurve old (d.P k (p.γ old)))
    (by positivity : 0 ≤ 3*K^4) hcoarse hcoarse1 hRate
    (hp.measurable_assignedClockCurve old (d.P k (p.γ old)))
    (packet.assignedSelectedEvent J) (packet.measurable_assignedSelectedEvent hJ)
    (packet.assignedSelectedEvent_unit_time hJF) hLip
  let J' := packet.originalCut J keep
  refine ⟨J',packet.measurable_originalCut hJ hkeep,packet.originalCut_subset J keep,?_,?_,hprior⟩
  · change (ENNReal.ofReal packet.unitFrame.q * d.ν k (p.γ old) packet.assigned)⁻¹ *
      ((d.ν k (p.γ old)).prod volume) (J \ packet.originalCut J keep) ≤ _
    rw [← packet.originalCut_loss (d.ν k (p.γ old)) hA hJ hJF hkeep,
      Broad.Source.FrozenPacket.assignedSelectedLaw, Measure.restrict_apply hkeep.compl]
    simpa only [measure_univ,mul_one,Set.sdiff_eq,inter_comm] using hloss
  · intro z hz
    rw [packet.assignedSelectedEvent_originalCut] at hz
    exact hlong z hz.2

end Problem

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
