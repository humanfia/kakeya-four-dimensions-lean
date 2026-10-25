-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripLists, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripLists.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripLists.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripLists.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripLists.lean.
   Original comments and attributions are preserved below. -/
import Submission.Lib.K4VelocityStrips

/-! Counting parent/strip/midpoint labels from the original observation.
The bound does not involve the total number of midpoint position bins. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open scoped BigOperators

def stripRawList {P : Type*} [DecidableEq P] {m : ℕ} (parents : Finset P)
    (bins : P → Fin m → Finset ℤ) : Finset (Σ _b : P, Σ _i : Fin m, ℤ) :=
  parents.sigma (fun b => Finset.univ.sigma (fun i => bins b i))

theorem stripRawList_card_le {P : Type*} [DecidableEq P] {m J : ℕ}
    (parents : Finset P) (bins : P → Fin m → Finset ℤ)
    (hbins : ∀ b ∈ parents, ∀ i, (bins b i).card ≤ J) :
    (stripRawList parents bins).card ≤ parents.card * (m * J) := by
  simp only [stripRawList, Finset.card_sigma]
  calc
    (∑ b ∈ parents, ∑ i : Fin m, (bins b i).card) ≤ ∑ _b ∈ parents, m * J := by
      apply Finset.sum_le_sum
      intro b hb
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbins b hb i)
    _ = _ := by simp

/-- Refinement labels counted at an observation inject into its finite parent,
strip and midpoint-bin lists. The ambient global bin range has no effect. -/
theorem strip_refined_label_count {P ι : Type} [DecidableEq P] [Fintype ι]
    {m J : ℕ} (parent : ι → P) (strip : ι → Fin m) (bin : ι → ℤ)
    (hcode : Function.Injective
      (fun a => (⟨parent a, ⟨strip a, bin a⟩⟩ : Σ _b : P, Σ _i : Fin m, ℤ)))
    (parents : Finset P) (bins : P → Fin m → Finset ℤ) (Good : ι → Prop)
    [DecidablePred Good]
    (hbins : ∀ b ∈ parents, ∀ i, (bins b i).card ≤ J)
    (hgood : ∀ a, Good a → parent a ∈ parents ∧ bin a ∈ bins (parent a) (strip a)) :
    (Finset.univ.filter Good).card ≤ parents.card * (m * J) := by
  apply (Finset.card_le_card_of_injOn
    (fun a => (⟨parent a, ⟨strip a, bin a⟩⟩ : Σ _b : P, Σ _i : Fin m, ℤ))
    (t := stripRawList parents bins) ?_ ?_).trans
      (stripRawList_card_le parents bins hbins)
  · intro a ha
    have h := hgood a (Finset.mem_filter.mp ha).2
    simpa only [Finset.mem_coe, stripRawList, Finset.mem_sigma, Finset.mem_univ, true_and] using h
  · exact fun _ _ _ _ h => hcode h

open Submission.Lib.K4VelocityStrips in
/-- The precise midpoint lists give the output multiplicity factor `2*C+1`,
uniformly in the number of charts, their locations and their frame parameters. -/
theorem strip_midpoint_label_count {P ι : Type} [DecidableEq P] [Fintype ι]
    {m : ℕ} (C : ℕ) (parent : ι → P) (strip : ι → Fin m) (bin : ι → ℤ)
    (hcode : Function.Injective
      (fun a => (⟨parent a, ⟨strip a, bin a⟩⟩ : Σ _b : P, Σ _i : Fin m, ℤ)))
    (parents : Finset P) (r : P → ℝ) (n : P → Fin m → StripSpace)
    (β : P → Fin m → ℝ) (t : P → ℝ) (Y : P → StripSpace) (Good : ι → Prop)
    [DecidablePred Good]
    (hgood : ∀ a, Good a → parent a ∈ parents ∧
      bin a ∈ midpointBinList (r (parent a)) (n (parent a) (strip a))
        (β (parent a) (strip a)) (t (parent a)) (Y (parent a)) C) :
    (Finset.univ.filter Good).card ≤ parents.card * (m * (2 * C + 1)) := by
  apply strip_refined_label_count parent strip bin hcode parents
    (fun b i => midpointBinList (r b) (n b i) (β b i) (t b) (Y b) C) Good _ hgood
  intro b _ i
  exact (midpointBinList_card _ _ _ _ _ C).le

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
