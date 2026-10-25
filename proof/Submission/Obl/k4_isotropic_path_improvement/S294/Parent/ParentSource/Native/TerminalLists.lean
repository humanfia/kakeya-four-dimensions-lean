-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.TerminalLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/TerminalLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/TerminalLists.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/TerminalLists.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/TerminalLists.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.MeasurableLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_dk4_smoothed_problem.Observation
import Submission.Lib.K4Homogenization.DyadicObservations

/-! Full old packet predictions are transferred to the terminal observation
before any later residual is selected. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4Homogenization
open scoped BigOperators

theorem obs_coarsen {Nk r L B : ℝ} (hNk : 1 ≤ Nk) (hrL : r ≤ L)
    (p : (ℕ × (Fin 6 → ℝ)) × ℝ) :
    obs B (δ Nk r) p = coarsenObservation Nk r L (obs B (δ Nk L) p) :=
  observation_factorization
    (fun p : (ℕ × (Fin 6 → ℝ)) × ℝ =>
      WithLp.toLp 2 ![p.2, (x p.1 p.2) 1, (x p.1 p.2) 2])
    (fun p => B * (x p.1 p.2) 3) hNk hrL p

noncomputable def terminalPacketList {W : ℕ} (p : PathData W) (Nk L : ℝ)
    (m : ℕ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (Fin p.C) :=
  Finset.univ.biUnion (fun i : Fin m => p.lst i w (coarsenObservation Nk (p.r i) L o))

theorem terminalPacketList_card {W : ℕ} (p : PathData W) (Nk L : ℝ) (m : ℕ)
    (hlist : ∀ i w o, ((p.lst i w o).card : ℝ) ≤ p.κ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((terminalPacketList p Nk L m w o).card : ℝ) ≤ m * p.κ := by
  classical
  calc
    _ ≤ ∑ i : Fin m, ((p.lst i w (coarsenObservation Nk (p.r i) L o)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin m, p.κ := Finset.sum_le_sum (fun i _ => hlist i w _)
    _ = _ := by simp

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.terminalPacketList_mem
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (hrL : ∀ i, i < m → p.r i ≤ L)
    (b : Fin p.C) (q : (ℕ × (Fin 6 → ℝ)) × ℝ) (hq : q ∈ p.F b) :
    b ∈ terminalPacketList p Nk L m (p.γ b) (obs (B (p.γ b)) (δ Nk L) q) := by
  classical
  rcases h.2.2.2.2.2.2.2 b with
    ⟨hlev, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpred, _⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨p.lev b, hlev⟩, Finset.mem_univ _, ?_⟩
  have hp := hpred q hq
  rw [obs_coarsen hNk (hrL _ hlev)] at hp
  exact hp

/-- The terminal observation has a measurable bounded list predicting EVERY
old packet in this world, fixed before any future incidence restriction. -/
theorem PathData.Valid.measurable_terminal_packet_list
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (hrL : ∀ i, i < m → p.r i ≤ L) (w : Fin W) :
    ∃ L' : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin p.C),
      (∀ b, MeasurableSet {o | b ∈ L' o}) ∧
      (∀ o, ((L' o).card : ℝ) ≤ m * p.κ) ∧
      ∀ b, p.γ b = w → ∀ q ∈ p.F b, b ∈ L' (obs (B w) (δ Nk L) q) := by
  classical
  let F : Fin p.C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    fun b => if p.γ b = w then p.F b else ∅
  have hF (b : Fin p.C) : MeasurableSet (F b) := by
    dsimp only [F]
    split
    · exact (h.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    · exact MeasurableSet.empty
  have hobs : Measurable (obs (B w) (δ Nk L)) :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_pureObservation _ _
  obtain ⟨L', hL', hc, hp⟩ := measurable_event_prediction_list
    (obs (B w) (δ Nk L)) hobs F hF (terminalPacketList p Nk L m w) (m * p.κ)
    (terminalPacketList_card p Nk L m h.2.2.2.2.2.1 w)
    (fun b q hq => by
      by_cases hb : p.γ b = w
      · have hq' : q ∈ p.F b := by simpa only [F, ite_eq_left hb] using hq
        simpa only [hb] using h.terminalPacketList_mem hNk hrL b q hq'
      · simp only [F, ite_eq_right hb, mem_empty_iff_false] at hq)
  refine ⟨L', hL', hc, ?_⟩
  intro b hb q hq
  exact hp b q (by simpa only [F, ite_eq_left hb] using hq)

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
