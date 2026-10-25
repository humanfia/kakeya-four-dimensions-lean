-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.Balance.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize
import Submission.WZ.Obl.wz_tower_balanced_refinement.Arithmetic

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

/-- Weighted balancing keeps whole fibres, so their existing local estimates survive. -/
lemma balance_whole_fibres {n N q : ℕ} (hq : 0 < q) {R : ℝ} (hR : 1 < R)
    (hn : (n : ℝ) < R ^ q) (S : Finset (Fin n)) (f : Fin n → Fin N)
    (w : Fin n → ℝ≥0∞) :
    ∃ S' : Finset (Fin n), S' ⊆ S ∧
      (∑ i ∈ S, w i) ≤ (q : ℝ≥0∞) * ∑ i ∈ S', w i ∧
      (∀ i ∈ S', ∀ j ∈ S, f i = f j → j ∈ S') ∧
      (∀ i ∈ S', ∀ j ∈ S',
        ((S'.filter (fun k => f k = f i)).card : ℝ) ≤
          R * (S'.filter (fun k => f k = f j)).card) := by
  classical
  obtain ⟨color, hcolor⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.exists_size_color n q R hq hR hn
  let c := fun i => color (S.filter (fun k => f k = f i)).card
  obtain ⟨b, hb⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color hq S c w
  let S' := S.filter (fun i => c i = b)
  have hS : S' ⊆ S := Finset.filter_subset _ _
  have hwhole : ∀ i ∈ S', ∀ j ∈ S, f i = f j → j ∈ S' := by
    intro i hi j hj hij
    have hci := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr ⟨hj, ?_⟩
    dsimp [c] at hci ⊢
    rwa [← hij]
  have hsame (i) (hi : i ∈ S') : S'.filter (fun k => f k = f i) = S.filter (fun k => f k = f i) := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hS h.1, h.2⟩, fun h => ⟨hwhole i hi k h.1 h.2.symm, h.2⟩⟩
  refine ⟨S', hS, hb, hwhole, ?_⟩
  intro i hi j hj
  rw [hsame i hi, hsame j hj]
  apply hcolor _ _
  · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hS hi, rfl⟩⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using Finset.card_le_univ S)
  · exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hS hj, rfl⟩⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using Finset.card_le_univ S)
  · exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

/-- The Katz--Tao condition in the unit ball supplies a polynomial cardinality bound. -/
lemma admissible_card_bound {d θ M L : ℝ} {n : ℕ} {x v : Fin n → Space}
    {Y : Fin n → Set Space} (hA : Admissible d θ M L x v Y) (hM : 0 ≤ M) :
    (n : ℝ) * d ^ 2 ≤ 8 * M := by
  have h := hA.2.2.2.2.1 (ball (0 : Space) 1) (convex_ball _ _)
  have he : {i | True ∧ tube d (x i) (v i) ⊆ ball (0 : Space) 1} = Set.univ := by
    ext i
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact ⟨trivial, (hA.2.1 i).2.1⟩
  rw [he, Set.ncard_univ, Nat.card_fin] at h
  have hball : volume (ball (0 : Space) 1) ≤ ENNReal.ofReal (8 : ℝ) := by
    rw [EuclideanSpace.volume_ball_fin_three]
    norm_num
    linarith [Real.pi_lt_four]
  have hh := h.trans (mul_le_mul_right hball (ENNReal.ofReal M))
  rw [← ENNReal.ofReal_mul hM] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh |>.trans_eq (mul_comm M 8)

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
