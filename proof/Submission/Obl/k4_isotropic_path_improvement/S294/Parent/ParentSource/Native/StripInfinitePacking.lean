-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripInfinitePacking, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripInfinitePacking.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripInfinitePacking.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripInfinitePacking.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripInfinitePacking.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4VelocityStrips

/-! Finite heavy-strip nets require no finiteness of the predicted state space.
The mass packing bound alone bounds the cardinality of every separated family. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

/-- A uniform bound for all finite separated families gives a finite maximal
family even when the original family is uncountable. -/
theorem exists_maximal_finite_pairwise {ι : Type*} (R : ι → ι → Prop)
    (hsymm : ∀ a b, R a b → R b a) (hirrefl : ∀ a, ¬ R a a) (C : ℕ)
    (hbound : ∀ s : Finset ι, (s : Set ι).Pairwise R → s.card ≤ C) :
    ∃ s : Finset ι, (s : Set ι).Pairwise R ∧ ∀ a, ∃ b ∈ s, ¬ R a b := by
  classical
  let cards := (Finset.range (C + 1)).filter
    (fun n => ∃ s : Finset ι, (s : Set ι).Pairwise R ∧ s.card = n)
  have hcards : cards.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact ⟨∅, by simp, rfl⟩
  have hk := (Finset.mem_filter.mp (cards.max'_mem hcards)).2
  obtain ⟨s, hs, hcard⟩ := hk
  refine ⟨s, hs, ?_⟩
  intro a
  by_contra! hfar
  have ha : a ∉ s := fun ha => hirrefl a (hfar a ha)
  have hins : ((insert a s : Finset ι) : Set ι).Pairwise R := by
    simpa only [Finset.coe_insert] using
      hs.insert (fun b hb _ => ⟨hfar b hb, hsymm a b (hfar b hb)⟩)
  have hn : (insert a s).card ∈ cards := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have h := hbound _ hins; omega), ?_⟩
    exact ⟨insert a s, hins, rfl⟩
  have hmax : (insert a s).card ≤ cards.max' hcards := cards.le_max' _ hn
  have hcardins := Finset.card_insert_of_notMem ha
  omega

/-- Apply the accepted finite probability packing bound to arbitrary finite
subfamilies, then choose a maximal one. No finite state encoder is needed. -/
theorem exists_short_heavy_strip_net_unrestricted {ι : Type*}
    (μ : Measure StripSpace) [IsProbabilityMeasure μ]
    (n : ι → StripSpace) (β : ι → ℝ) {κ ε r ρ T : ℝ}
    (hn : ∀ i, ‖n i‖ = 1) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ i, κ ≤ μ.real (boundedStrip (n i) (β i) r T))
    (hcap : ∀ x, μ (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ s : Finset ι, (s.card : ℝ) ≤ 2 / κ ^ 2 ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ρ ≤ ‖n i - n j‖ + |β i - β j| ∧ ρ ≤ ‖n i + n j‖ + |β i + β j|) ∧
      ∀ i, ∃ j ∈ s,
        ‖n i - n j‖ + |β i - β j| < ρ ∨ ‖n i + n j‖ + |β i + β j| < ρ := by
  classical
  let sep : ι → ι → Prop := fun i j =>
    ρ ≤ ‖n i - n j‖ + |β i - β j| ∧ ρ ≤ ‖n i + n j‖ + |β i + β j|
  have hsize (s : Finset ι) (hs : (s : Set ι).Pairwise sep) :
      (s.card : ℝ) ≤ 2 / κ ^ 2 := by
    have h := heavy_strips_card_le μ (fun i : s => n i) (fun i : s => β i)
      (fun i => hn i) hκ hε hT hρ hsmall (fun i => hmass i)
      (fun i j hij => hs i.property j.property (fun h => hij (Subtype.ext h))) hcap heps
    simpa only [Fintype.card_coe] using h
  obtain ⟨s, hs, hcover⟩ := exists_maximal_finite_pairwise sep
    (fun i j h => by simpa only [sep, norm_sub_rev, abs_sub_comm, add_comm] using h)
    (fun i h => by
      have hzero := h.1
      simp only [sub_self, norm_zero, abs_zero, zero_add] at hzero
      linarith)
    ⌈2 / κ ^ 2⌉₊
    (fun s hs => by exact_mod_cast (hsize s hs).trans (Nat.le_ceil (2 / κ ^ 2)))
  refine ⟨s, hsize s hs, hs, ?_⟩
  intro i
  obtain ⟨j, hj, hnear⟩ := hcover i
  exact ⟨j, hj, by simpa only [sep, not_and_or, not_le] using hnear⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
