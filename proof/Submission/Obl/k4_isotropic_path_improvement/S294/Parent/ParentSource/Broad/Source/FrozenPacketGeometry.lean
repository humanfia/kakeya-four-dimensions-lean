-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FrozenPacketGeometry, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FrozenPacketGeometry.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FrozenPacketGeometry.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPacketGeometry.lean.
-- Existing source attributions are preserved below.

import Submission.Lib.K4XInterface.Basic
import Submission.Lib.K4ChartLifting.Normalized
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.NativeSignal

/-!
The native unit-block geometry of an actual frozen chart. The old
indexed trajectory and the old quadratic test determine every function.

Adapted from this LOT tree, o204, session x0747, branch x0747,
commit b5bc2d88, `Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketGeometry.lean`.
That file's path interface is replaced by the accepted frozen `gchart`
interface, so this construction also applies directly to o106's level-zero path.
The normalization theorems themselves are imported from K4ChartLifting.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4XInterface

noncomputable section

/-- One original chart, with exactly its frozen single-chart certificate. -/
structure FrozenPacket where
  size : ℝ
  formatExponent : ℕ
  formatDegree : ℕ
  slack : ℝ
  timeDepth : ℕ
  timeBin : ℝ
  depth : ℝ
  derivativeScale : ℝ
  originalEvent : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  center : EuclideanSpace ℝ (Fin 2)
  speed : EuclideanSpace ℝ (Fin 2)
  matrix : Matrix (Fin 2) (Fin 2) ℝ
  originalTest : MvPolynomial (Fin 4) ℝ
  assigned : Set (ℕ × (Fin 6 → ℝ))
  counted : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  valid : gchart size formatExponent formatDegree slack timeDepth timeBin depth
    derivativeScale originalEvent center speed matrix originalTest assigned counted True

namespace FrozenPacket

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Line × ℝ

def unitFrame (p : FrozenPacket) : Submission.Lib.K4ChartLifting.Frame where
  t₀ := p.timeBin / (2 : ℝ) ^ p.timeDepth
  q := ((2 : ℝ) ^ p.timeDepth)⁻¹
  c := p.center
  u := p.speed
  D := p.matrix

theorem unitFrame_length_pos (p : FrozenPacket) : 0 < p.unitFrame.q := by
  dsimp [unitFrame]
  positivity

theorem unitFrame_det (p : FrozenPacket) : IsUnit p.unitFrame.D.det :=
  isUnit_iff_ne_zero.mpr p.valid.1

def line (p : FrozenPacket) (l : Line) : Line := p.unitFrame.normTraj l

def test (p : FrozenPacket) : MvPolynomial (Fin 4) ℝ :=
  p.unitFrame.normTest (gδ p.size p.depth) p.originalTest

def position (p : FrozenPacket) (l : Line) : Fin 3 → ℝ :=
  fun a => gx (p.line l) 0 a.castSucc

def velocity (p : FrozenPacket) (l : Line) : Fin 3 → ℝ :=
  ![1, (p.line l).2 3, (p.line l).2 4]

def base (p : FrozenPacket) (l : Line) (t : ℝ) : Fin 3 → ℝ :=
  fun a => gx (p.line l) t a.castSucc

def signal (p : FrozenPacket) (l : Line) : Polynomial ℝ :=
  SixPath.nativeSignalPolynomial p.test (p.line l)

def signalValue (p : FrozenPacket) (l : Line) (t : ℝ) : ℝ :=
  eval (gx (p.line l) t) p.test

theorem velocity_time (p : FrozenPacket) (l : Line) : p.velocity l 0 = 1 := rfl

theorem base_motion (p : FrozenPacket) (l : Line) (t : ℝ) :
    p.base l t = fun a => p.position l a + t * p.velocity l a := by
  funext a
  fin_cases a <;> simp [base, position, velocity, gx]

theorem measurable_line (p : FrozenPacket) : Measurable p.line :=
  Submission.Lib.K4ChartLifting.ChartSystem.measurable_normTraj _

theorem measurable_base (p : FrozenPacket) :
    Measurable (fun z : Incidence => p.base z.1 z.2) := by
  have hL : Measurable (fun z : Incidence => p.line z.1) :=
    p.measurable_line.comp measurable_fst
  have hc (j : Fin 6) : Measurable (fun z : Incidence => (p.line z.1).2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp hL)
  apply measurable_pi_iff.mpr
  intro a
  fin_cases a
  · exact measurable_snd
  · exact (hc 0).add (measurable_snd.mul (hc 3))
  · exact (hc 1).add (measurable_snd.mul (hc 4))

theorem measurable_signalValue (p : FrozenPacket) :
    Measurable (fun z : Incidence => p.signalValue z.1 z.2) := by
  have hL : Measurable (fun z : Incidence => p.line z.1) :=
    p.measurable_line.comp measurable_fst
  have hc (j : Fin 6) : Measurable (fun z : Incidence => (p.line z.1).2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp hL)
  have hpoint : Measurable (fun z : Incidence => gx (p.line z.1) z.2) := by
    apply measurable_pi_iff.mpr
    intro a
    fin_cases a
    · exact measurable_snd
    · exact (hc 0).add (measurable_snd.mul (hc 3))
    · exact (hc 1).add (measurable_snd.mul (hc 4))
    · exact (hc 2).add (measurable_snd.mul (hc 5))
  exact (MvPolynomial.continuous_eval p.test).measurable.comp hpoint

theorem eval_signal (p : FrozenPacket) (l : Line) (t : ℝ) :
    (p.signal l).eval t = p.signalValue l t :=
  SixPath.eval_nativeSignalPolynomial p.test (p.line l) t

theorem test_degree (p : FrozenPacket) : p.test.totalDegree ≤ 2 := by
  rcases p.valid with ⟨_, _, _, _, hdeg, _⟩
  exact (p.unitFrame.totalDegree_normTest_le _ _).trans hdeg

theorem signal_degree (p : FrozenPacket) (l : Line) : (p.signal l).natDegree ≤ 2 :=
  SixPath.degree_nativeSignalPolynomial p.test (p.line l) p.test_degree

theorem unit_time_mem (p : FrozenPacket) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p.unitFrame.t₀ + p.unitFrame.q * t ∈
      Icc (p.timeBin / (2 : ℝ) ^ p.timeDepth)
        ((p.timeBin + 1) / (2 : ℝ) ^ p.timeDepth) := by
  have hq := p.unitFrame_length_pos
  have hr : p.unitFrame.t₀ + p.unitFrame.q =
      (p.timeBin + 1) / (2 : ℝ) ^ p.timeDepth := by
    dsimp [unitFrame]
    ring
  change p.unitFrame.t₀ ≤ p.unitFrame.t₀ + p.unitFrame.q * t ∧ _
  rw [← hr]
  constructor <;> nlinarith [ht.1, ht.2]

/-- Whole-time native bounds depend on the original chart slack, rather
than the original coefficient and format envelopes. -/
theorem native_bounds (p : FrozenPacket) (l : Line) (hl : l ∈ p.assigned)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖gy (p.line l) t‖ + ‖gv (p.line l)‖ ≤ 3 * p.slack ∧
      |p.signalValue l t| ≤ p.slack ∧
      |eval (gx (p.line l) t) (pderiv 3 p.test)| ≤
        p.slack * (p.derivativeScale / gδ p.size p.depth) ∧
      |eval (gx (p.line l) t) (pderiv 3 (pderiv 3 p.test))| ≤
        p.slack * (p.derivativeScale / gδ p.size p.depth) ^ 2 := by
  rcases p.valid with ⟨_, _, _, _, _, _, _, _, _, hwhole, _, _⟩
  have hr : p.unitFrame.t₀ + p.unitFrame.q =
      (p.timeBin + 1) / (2 : ℝ) ^ p.timeDepth := by dsimp [unitFrame]; ring
  have hfit : ∀ τ ∈ Icc p.unitFrame.t₀ (p.unitFrame.t₀ + p.unitFrame.q),
      ‖Matrix.toEuclideanLin p.unitFrame.D⁻¹
        (Submission.Lib.K4ChartLifting.planarPoint l τ - p.unitFrame.c - τ • p.unitFrame.u)‖
        ≤ p.slack := by
    intro τ hτ
    have hτ' : τ ∈ Icc (p.timeBin / (2 : ℝ) ^ p.timeDepth)
        ((p.timeBin + 1) / (2 : ℝ) ^ p.timeDepth) := by
      exact ⟨hτ.1, hr ▸ hτ.2⟩
    exact ((hwhole l hl).2.2 τ hτ').1
  have hplan := Submission.Lib.K4ChartLifting.norm_planar_add_velocity_le
    (fun τ hτ => p.unitFrame.norm_planar_normTraj_le p.unitFrame_length_pos l hfit τ hτ)
    t ht
  obtain ⟨_, hval, hfirst, hsecond⟩ := (hwhole l hl).2.2 _ (p.unit_time_mem ht)
  have hnative := p.unitFrame.normTest_bounds p.unitFrame_length_pos.ne' p.unitFrame_det
    (gδ_pos p.size p.depth) p.originalTest l t hval hfirst hsecond
  exact ⟨hplan, hnative⟩

theorem measurable_assigned (p : FrozenPacket) : MeasurableSet p.assigned := by
  rcases p.valid with ⟨_, _, _, _, _, _, hA, _⟩
  exact hA

theorem measurable_counted (p : FrozenPacket) : MeasurableSet p.counted := by
  rcases p.valid with ⟨_, _, _, _, _, _, _, hF, _⟩
  exact hF

theorem counted_inside_original (p : FrozenPacket) {z : Incidence} (hz : z ∈ p.counted) :
    z ∈ p.originalEvent ∧ z.1 ∈ p.assigned ∧
      z.2 ∈ Icc p.unitFrame.t₀ (p.unitFrame.t₀ + p.unitFrame.q) := by
  rcases p.valid with ⟨_, _, _, _, _, _, _, _, _, _, hcount, _⟩
  obtain ⟨hE, hA, ht, _⟩ := hcount z hz
  refine ⟨hE, hA, ht.1, ?_⟩
  have hr : p.unitFrame.t₀ + p.unitFrame.q =
      (p.timeBin + 1) / (2 : ℝ) ^ p.timeDepth := by dsimp [unitFrame]; ring
  rw [hr]
  exact ht.2

end FrozenPacket

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source
