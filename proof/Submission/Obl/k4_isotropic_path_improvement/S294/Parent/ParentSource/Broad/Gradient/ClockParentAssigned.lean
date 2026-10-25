-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ClockParentAssigned, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ClockParentAssigned.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit c5f477fdc5b972684b967b4654ceacc9f5a8f0ff,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ClockParentAssigned.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentPrior
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.CoarseGeometry

/-! # The literal parent curve on the complete old assignment -/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
open MeasureTheory Set Native Broad.Source
noncomputable section

/-- The coefficient curve is the unsheared original base together with
the physical parent signal in old clock units. -/
theorem clockPacket_point {W : ℕ} {P : Po} (hP : P.totalDegree ≤ 2)
    (p : PathData W) (old : Fin p.C) (q : Ev) :
    Jets2.coefficientPhysical (clockPacketCoefficients P p old q.1) (packetTime p old q) =
      WithLp.toLp 2 ![unshearedPacketBase p old q 0,
        unshearedPacketBase p old q 1,unshearedPacketBase p old q 2,
        (2:ℝ)^p.T (p.lev old)*MvPolynomial.eval (xp q.1 q.2) P] := by
  have hb := clockPacket_base P p old q
  ext j
  fin_cases j
  · rfl
  · exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hb
  · exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hb
  · exact clockPacket_signal hP p old q

section Original
variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

def assignedClockCoefficients (old : Fin p.C) (l : (hp.frozenPacket old).AssignedLine) :
    Fin 7 → ℝ :=
  safeClockCoefficients (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) p old (l : Ln)

theorem measurable_assignedClockCoefficients (old : Fin p.C) :
    Measurable (assignedClockCoefficients hp old) :=
  (measurable_safeClockCoefficients _ _ _ _ _).comp measurable_subtype_coe

theorem assignedClockCoefficients_eq (old : Fin p.C)
    {l : (hp.frozenPacket old).AssignedLine}
    (hl : (l : Ln) ∈ clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))) :
    assignedClockCoefficients hp old l=clockPacketCoefficients (d.P k (p.γ old)) p old l :=
  safeClockCoefficients_eq _ _ _ _ _ hl

variable (hd : d.Valid)
include hd

/-- All four analytic jets have a uniform original subpower bound on
every label of the unchanged complete old assignment. -/
theorem assignedClockCoefficients_jets (old : Fin p.C)
    (l : (hp.frozenPacket old).AssignedLine) :
    |assignedClockCoefficients hp old l 1| ≤ 24*d.K k ∧
    |assignedClockCoefficients hp old l 2| ≤ 24*d.K k ∧
    |assignedClockCoefficients hp old l 4| ≤ 24*d.K k ∧
    |assignedClockCoefficients hp old l 6| ≤ 24*d.K k := by
  have hP := (original_parent_bounds (show pb d.N d.K d.L d.d d.S d.η d.W d.ω
    d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  exact safeClockCoefficients_jets hP p old (hp.2.2.2.2.2.2.2 old).2.1
    (zero_le_one.trans (hd.2.2.1.1 k)) l

theorem assignedClock_point (old : Fin p.C)
    (z : (hp.frozenPacket old).AssignedLine×ℝ)
    (hz : (z.1 : Ln) ∈ clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))) :
    Jets2.coefficientPhysical (assignedClockCoefficients hp old z.1) z.2 =
      WithLp.toLp 2 ![unshearedPacketBase p old ((hp.frozenPacket old).originalIncidence z) 0,
        unshearedPacketBase p old ((hp.frozenPacket old).originalIncidence z) 1,
        unshearedPacketBase p old ((hp.frozenPacket old).originalIncidence z) 2,
        (2:ℝ)^p.T (p.lev old)*MvPolynomial.eval
          (xp ((hp.frozenPacket old).originalIncidence z).1
            ((hp.frozenPacket old).originalIncidence z).2) (d.P k (p.γ old))] := by
  have hP := (original_parent_bounds (show pb d.N d.K d.L d.d d.S d.η d.W d.ω
    d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  rw [assignedClockCoefficients_eq hp old hz]
  have hh := clockPacket_point hP p old ((hp.frozenPacket old).originalIncidence z)
  rw [hp.originalIncidence_time old z,(hp.frozenPacket old).originalIncidence_fst] at hh
  exact hh

/-- The derivative used by MK4 is exactly the original physical parent
rate, without an inverse old height or inverse clock loss. -/
theorem assignedClock_rate (old : Fin p.C)
    (z : (hp.frozenPacket old).AssignedLine×ℝ)
    (hz : (z.1 : Ln) ∈ clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))) :
    assignedClockCoefficients hp old z.1 1+2*assignedClockCoefficients hp old z.1 2*z.2 =
      rate (d.P k (p.γ old)) ((hp.frozenPacket old).originalIncidence z).1
        ((hp.frozenPacket old).originalIncidence z).2 := by
  have hP := (original_parent_bounds (show pb d.N d.K d.L d.d d.S d.η d.W d.ω
    d.ν d.E d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  rw [assignedClockCoefficients_eq hp old hz]
  have hh := clockPacket_rate hP p old ((hp.frozenPacket old).originalIncidence z)
  rw [hp.originalIncidence_time old z,(hp.frozenPacket old).originalIncidence_fst] at hh
  exact hh

omit hd in
theorem assignedClock_velocity (old : Fin p.C)
    (l : (hp.frozenPacket old).AssignedLine)
    (hl : (l : Ln) ∈ clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old))) :
    Jets2.zv (assignedClockCoefficients hp old l)=fun j => v (l : Ln) j := by
  rw [assignedClockCoefficients_eq hp old hl]
  exact clockPacket_velocity _ _ _ _

end Original
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
