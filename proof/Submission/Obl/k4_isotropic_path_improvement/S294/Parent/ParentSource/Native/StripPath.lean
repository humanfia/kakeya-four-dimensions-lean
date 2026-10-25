-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPath, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPath.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPath.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPath.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPath.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Frames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.TerminalLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAtlas

/-! The original path at one fixed level supplies the concrete parent family.
Its terminal lists retain the actual path cap without a total-family factor. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators

abbrev PathData.StripLevel {W : ℕ} (p : PathData W) (i : ℕ) := {b : Fin p.C // p.lev b = i}

def PathData.stripParent {W : ℕ} (p : PathData W) (i : ℕ) (b : p.StripLevel i) :
    StripParent W (p.T i) where
  world := p.γ b
  timeIndex := ⟨p.j b % (2 ^ p.T i), Nat.mod_lt _ (by positivity)⟩
  center := p.c b
  velocity := p.u b
  frame := p.Q b
  test := p.R b
  trajectories := p.A b
  incidences := p.F b

open Classical in
def PathData.stripParentList {W : ℕ} (p : PathData W) (N L : ℝ) (i : ℕ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (p.StripLevel i) :=
  (p.lst i w (Submission.Lib.K4Homogenization.coarsenObservation N (p.r i) L o)).subtype
    (fun b => p.lev b = i)

section Path

variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.stripParent_valid
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (i : ℕ) (b : p.StripLevel i) :
    (p.stripParent i b).Valid N Mp Dp p.κ (p.r i) B E := by
  have hb := h.2.2.2.2.2.2.2 b.val
  have hj := hb.2.1
  have hc := hb.2.2
  rw [b.property] at hj hc
  dsimp only [StripParent.Valid, PathData.stripParent]
  rw [Nat.mod_eq_of_lt hj]
  rcases hc with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, True.intro⟩

theorem PathData.Valid.stripParent_disjoint
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (i : ℕ)
    (b b' : p.StripLevel i) (hne : b ≠ b')
    (hw : (p.stripParent i b).world = (p.stripParent i b').world)
    (ht : (p.stripParent i b).timeIndex = (p.stripParent i b').timeIndex) :
    Disjoint (p.stripParent i b).trajectories (p.stripParent i b').trajectories := by
  have hj : p.j b < 2 ^ p.T i := by
    simpa only [b.property] using (h.2.2.2.2.2.2.2 b.val).2.1
  have hj' : p.j b' < 2 ^ p.T i := by
    simpa only [b'.property] using (h.2.2.2.2.2.2.2 b'.val).2.1
  have heq : p.j b = p.j b' := by
    have hnat := congrArg Fin.val ht
    simpa only [PathData.stripParent, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] using hnat
  exact h.2.2.2.2.2.2.1 b b' (fun h => hne (Subtype.ext h))
    (b.property.trans b'.property.symm) hw heq

open Classical in
theorem PathData.Valid.stripParentList_card
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (i : ℕ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((p.stripParentList N L i w o).card : ℝ) ≤ p.κ := by
  have hc : (p.stripParentList N L i w o).card ≤
      (p.lst i w (Submission.Lib.K4Homogenization.coarsenObservation N (p.r i) L o)).card := by
    rw [PathData.stripParentList, Finset.card_subtype]
    exact Finset.card_filter_le _ _
  exact (Nat.cast_le.mpr hc).trans (h.2.2.2.2.2.1 i w _)

theorem PathData.Valid.stripParentList_known
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 1 ≤ N) (i : ℕ) (hrL : p.r i ≤ L)
    (b : p.StripLevel i) (x : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hx : x ∈ (p.stripParent i b).incidences) :
    b ∈ p.stripParentList N L i (p.stripParent i b).world
      (gobs (B (p.stripParent i b).world) (gδ N L) x) := by
  classical
  rcases h.2.2.2.2.2.2.2 b.val with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpred, _⟩
  have hp := hpred x hx
  rw [b.property, obs_coarsen hN hrL] at hp
  exact Finset.mem_subtype.mpr hp

theorem PathData.Valid.stripParent_velocity_bound
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (i : ℕ)
    (b : p.StripLevel i) (l : ℕ × (Fin 6 → ℝ))
    (hl : l ∈ (p.stripParent i b).trajectories) :
    ‖packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
      (p.stripParent i b).velocity l‖ ≤ 2 * p.κ := by
  simpa only [packetVelocity, PathData.stripParent, b.property, v, gv] using
    h.normalized_velocity_bound b.val l hl

theorem PathData.Valid.stripParent_determinant_bound
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (i : ℕ) (b : p.StripLevel i) :
    |(p.stripParent i b).frame.det| * (4 : ℝ) ^ p.T i ≤
      N ^ (-(p.nw i) + δ₀ * L) := by
  rcases h.2.2.2.2.2.2.2 b.val with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hup, _⟩
  have he : -(p.nw i - δ₀ * L) = -(p.nw i) + δ₀ * L := by ring
  simpa only [PathData.stripParent, b.property, he] using hup

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
