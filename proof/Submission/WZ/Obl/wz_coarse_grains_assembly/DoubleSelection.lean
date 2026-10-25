-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.DoubleSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Packing
import Submission.WZ.Obl.wz_coarse_grains_assembly.Restrict
import Submission.WZ.Obl.wz_separated_cover_refinement.Selection
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

/-- A fixed palette separates coarse tubes after doubling their radii. -/
theorem doubled_tube_coloring {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {N : ℕ} (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w) :
    ∃ color : Fin N → Fin (10 ^ 40 + 1),
      ∀ k k', k ≠ k' → color k = color k' →
        μ (T (2 * ρ) (y k) (w k) ∩ T (2 * ρ) (y k') (w k')) ≤
          1 / 2 * μ (T (2 * ρ) (y k) (w k)) := by
  classical
  let R (k k' : Fin N) : Prop :=
    1 / 2 * μ (T (2 * ρ) (y k) (w k)) <
        μ (T (2 * ρ) (y k) (w k) ∩ T (2 * ρ) (y k') (w k')) ∨
      1 / 2 * μ (T (2 * ρ) (y k') (w k')) <
        μ (T (2 * ρ) (y k) (w k) ∩ T (2 * ρ) (y k') (w k'))
  have hsymm : ∀ {k k'}, R k k' → R k' k := by
    intro k k' h
    dsimp only [R] at h ⊢
    rw [Set.inter_comm (T (2 * ρ) (y k') (w k'))]
    exact h.elim Or.inr Or.inl
  have hdegree : ∀ k, (Finset.univ.filter (R k)).card < 10 ^ 40 + 1 := by
    intro k
    exact Nat.lt_succ_of_le (conflict_card hρ hρ1 y w hw hX k)
  obtain ⟨color, hc⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.color_relation
    (by positivity : 0 < 10 ^ 40 + 1) R hsymm (fun k => by
      convert hdegree k using 1 <;> congr)
  refine ⟨color, ?_⟩
  intro k k' hne heq
  exact le_of_not_gt (fun h => hc k k' hne (Or.inl h) heq)

/-- An arbitrary weighted collection has a nonempty subcollection that is
essentially distinct at twice the radius, with a fixed loss of weight. -/
theorem doubled_distinct_selection {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    {N : ℕ} (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1) (hX : X ρ N y w)
    (B : Finset (Fin N)) (weight : Fin N → ENNReal)
    (hpos : 0 < ∑ k ∈ B, weight k) :
    ∃ A : Finset (Fin N), A ⊆ B ∧ A.Nonempty ∧
      (∑ k ∈ B, weight k) ≤ ((10 ^ 40 + 1 : ℕ) : ENNReal) * ∑ k ∈ A, weight k ∧
      ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' →
        μ (T (2 * ρ) (y k) (w k) ∩ T (2 * ρ) (y k') (w k')) ≤
          1 / 2 * μ (T (2 * ρ) (y k) (w k)) := by
  classical
  obtain ⟨color, hc⟩ := doubled_tube_coloring hρ hρ1 y w hw hX
  obtain ⟨a, ha⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    (by positivity : 0 < 10 ^ 40 + 1) B color weight
  refine ⟨B.filter (fun k => color k = a), Finset.filter_subset _ _, ?_, ha, ?_⟩
  · by_contra hempty
    have he : B.filter (fun k => color k = a) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [he, Finset.sum_empty, mul_zero] at ha
    exact (not_le_of_gt hpos) ha
  · intro k hk k' hk' hne
    exact hc k k' hne ((Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hk').2.symm)

/-- The selected family also has uniformly bounded containment multiplicity.
The count is over the original coarse indices. -/
theorem selected_doubled_multiplicity {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρ1 : ρ ≤ 1 / 2) {N : ℕ} (y w : Fin N → V) (hw : ∀ k, ‖w k‖ = 1)
    (A : Finset (Fin N))
    (hX : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' →
      μ (T (2 * ρ) (y k) (w k) ∩ T (2 * ρ) (y k') (w k')) ≤
        1 / 2 * μ (T (2 * ρ) (y k) (w k)))
    (x v : V) (hv : ‖v‖ = 1) :
    q N {k | k ∈ A ∧ T δ x v ⊆ T (2 * ρ) (y k) (w k)} ≤ 10 ^ 15 := by
  rw [← q_rIdx A (fun k => T δ x v ⊆ T (2 * ρ) (y k) (w k))]
  apply mult_ncard hδ (by linarith) (by linarith)
    (fun k => y (rIdx A k)) (fun k => w (rIdx A k)) (fun k => hw _) _ x v hv
  intro k k' hne
  exact hX _ (rIdx_mem A k) _ (rIdx_mem A k')
    (fun he => hne (rIdx_injective A he))

end WangZahlLot.Obl.wz_coarse_grains_assembly
