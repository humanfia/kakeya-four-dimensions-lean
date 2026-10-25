-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Localization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Equivariance

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped BigOperators

/-- A fixed finite partition of the bounded position-direction parameter space
has a dense nonempty cell of arbitrarily small diameter. -/
theorem dense_parameter_cell {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n : ℕ) (x v : Fin n → Space),
      (∀ i, ‖x i‖ ≤ 1 ∧ ‖v i‖ ≤ 1) →
      ∀ G : Finset (Fin n), G.Nonempty →
      ∃ S : Finset (Fin n), S ⊆ G ∧ S.Nonempty ∧ G.card ≤ K * S.card ∧
        ∀ i ∈ S, ∀ j ∈ S, ‖x i - x j‖ < ε ∧ ‖v i - v j‖ < ε := by
  classical
  have hc := (isCompact_closedBall (0 : Space × Space) 1).totallyBounded
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hc (ε / 2) (by positivity)
  letI := ht.fintype
  have htne : Nonempty t := by
    have hz := hcover (show (0 : Space × Space) ∈ closedBall 0 1 by simp)
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hct, _⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨c, hct⟩⟩
  letI := htne
  refine ⟨Fintype.card t, Fintype.card_pos, ?_⟩
  intro n x v hbound G hG
  have hex (i : Fin n) : ∃ c : t, dist (x i, v i) c.val < ε / 2 := by
    have hi : (x i, v i) ∈ closedBall (0 : Space × Space) 1 := by
      simpa only [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using hbound i
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hi)
    obtain ⟨hct, hball⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨c, hct⟩, hball⟩
  choose color hcolor using hex
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun c : t => (G.filter fun i => color i = c).card) Finset.univ_nonempty
  let S := G.filter fun i => color i = c
  have hcard : G.card ≤ Fintype.card t * S.card := by
    calc
      G.card = ∑ c : t, (G.filter fun i => color i = c).card :=
        Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
      _ ≤ ∑ _c : t, S.card := Finset.sum_le_sum (fun c hc => hmax c hc)
      _ = Fintype.card t * S.card := by simp
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have he : S.card = 0 := by omega
    rw [he, mul_zero] at hcard
    have := Finset.card_pos.mpr hG
    omega
  refine ⟨S, Finset.filter_subset _ _, hS, hcard, ?_⟩
  intro i hi j hj
  have hci := (Finset.mem_filter.mp hi).2
  have hcj := (Finset.mem_filter.mp hj).2
  have hi' : dist (x i, v i) c.val < ε / 2 := by simpa only [hci] using hcolor i
  have hj' : dist c.val (x j, v j) < ε / 2 := by
    simpa only [hcj, dist_comm c.val] using hcolor j
  have hd : dist (x i, v i) (x j, v j) < ε :=
    (dist_triangle _ c.val _).trans_lt (by linarith)
  rw [Prod.dist_eq, max_lt_iff] at hd
  simpa only [dist_eq_norm] using hd

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
