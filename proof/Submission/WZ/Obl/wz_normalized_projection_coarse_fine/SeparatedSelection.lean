-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.SeparatedSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_cover_refinement.Selection

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Bounded local multiplicity permits weighted separation with a fixed finite loss. -/
theorem separated_weighted_subset {α E : Type*} [DecidableEq α] [PseudoMetricSpace E]
    (U : Finset α) (q : α → E) (w : α → ℝ) {r : ℝ} {K : ℕ}
    (hcount : ∀ a ∈ U, (U.filter (fun b => q b ∈ Metric.ball (q a) r)).card ≤ K) :
    ∃ V ⊆ U, (∑ a ∈ U, w a) ≤ ((K + 1 : ℕ) : ℝ) * ∑ a ∈ V, w a ∧
      ∀ a ∈ V, ∀ b ∈ V, a ≠ b → r ≤ dist (q a) (q b) := by
  classical
  let R (a b : {a // a ∈ U}) := dist (q a) (q b) < r
  have hR : ∀ {a b}, R a b → R b a := by
    intro a b h
    simpa only [R, dist_comm] using h
  have hU : (Finset.univ : Finset {a // a ∈ U}) = U.attach := by ext a; simp
  have hdegree (a : {a // a ∈ U}) : (Finset.univ.filter (R a)).card < K + 1 := by
    have he : (Finset.univ.filter (R a)).card =
        (U.filter (fun b => q b ∈ Metric.ball (q a) r)).card := by
      refine Finset.card_bij (fun b _ => b.val) ?_ ?_ ?_
      · intro b hb
        exact Finset.mem_filter.mpr ⟨b.property,
          by simpa only [R, Metric.mem_ball, dist_comm] using (Finset.mem_filter.mp hb).2⟩
      · intro b hb c hc hbc
        exact Subtype.ext hbc
      · intro b hb
        refine ⟨⟨b, (Finset.mem_filter.mp hb).1⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by simpa only [R, Metric.mem_ball, dist_comm] using (Finset.mem_filter.mp hb).2⟩
    rw [he]
    exact Nat.lt_succ_of_le (hcount a a.property)
  obtain ⟨c, hc⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.color_relation
    (Nat.succ_pos K) R hR hdegree
  obtain ⟨k, hk⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.heavy_fibre c
    (fun a => w a)
  let S := Finset.univ.filter (fun a => c a = k)
  let e : {a // a ∈ U} ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  let V := S.map e
  have hVU : V ⊆ U := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    exact b.property
  refine ⟨V, hVU, ?_, ?_⟩
  · have hsum : ∑ a ∈ V, w a = ∑ a ∈ S, w a := by
      exact Finset.sum_map S e w
    rw [hsum]
    simp only [Fintype.card_fin, hU, Finset.sum_attach] at hk
    convert hk using 1
    congr 1
    apply Finset.sum_congr
    · ext a
      simp [S, hU]
    · intro a ha
      rfl
  · intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    have hij : i ≠ j := by intro h; exact hab (congrArg e h)
    have hci : c i = k := (Finset.mem_filter.mp hi).2
    have hcj : c j = k := (Finset.mem_filter.mp hj).2
    by_contra hdist
    exact hc i j hij (lt_of_not_ge hdist) (hci.trans hcj.symm)

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
