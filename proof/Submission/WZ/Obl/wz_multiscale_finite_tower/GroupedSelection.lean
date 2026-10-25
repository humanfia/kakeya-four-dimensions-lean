-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.GroupedSelection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.WeightedCards
import Submission.WZ.Obl.wz_multiscale_finite_tower.HierarchyRestriction

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)

/-- A family of whole groups, each represented by one of its children. -/
structure GroupedSelection {n m : ℕ} (parent : Fin n → Fin m) (H B : ℝ) where
  parents : Finset (Fin m)
  selected : Finset (Fin n)
  group : Fin n → Fin n
  parent_group : ∀ i, parent (group i) = parent i
  selected_parent : ∀ i ∈ selected, parent i ∈ parents
  group_mem : ∀ i ∈ selected, group i ∈ selected
  group_idem : ∀ i ∈ selected, group (group i) = group i
  retained : ∀ k ∈ parents, H * (Finset.univ.filter (fun i => parent i = k)).card ≤
    (selected.filter (fun i => parent i = k)).card
  balanced : ∀ i ∈ selected, ∀ j ∈ selected, parent i = parent j →
    ((selected.filter (fun a => group a = group i)).card : ℝ) ≤
      B * (selected.filter (fun a => group a = group j)).card

lemma leafFiber_closed {α β : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p : α → β)
    (hc : ∀ i ∈ S, ∀ j, p j = p i → j ∈ S) {i : α} (hi : i ∈ S) :
    leafFiber S p i = leafFiber Finset.univ p i := by
  classical
  ext j
  simp only [leafFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨hc i hi j h, h⟩⟩

lemma balanced_of_closed {α β : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p : α → β) {R : ℝ}
    (hc : ∀ i ∈ S, ∀ j, p j = p i → j ∈ S)
    (h : Balanced Finset.univ p R) : Balanced S p R := by
  intro i hi j hj
  rw [leafFiber_closed S p hc hi, leafFiber_closed S p hc hj]
  exact h i (Finset.mem_univ _) j (Finset.mem_univ _)

lemma balanced_mono {α β : Type*} [DecidableEq α] {S : Finset α} {p : α → β}
    {R R' : ℝ} (h : Balanced S p R) (hRR : R ≤ R') : Balanced S p R' := by
  intro i hi j hj
  exact (h i hi j hj).trans (mul_le_mul_of_nonneg_right hRR (Nat.cast_nonneg _))

/-- Retaining a fraction of child nodes retains a comparable fraction of leaves. -/
lemma GroupedSelection.leaf_retention {J k : ℕ} {T : TubeHierarchy J}
    {H B R μ : ℝ} (G : GroupedSelection (T.parent k) H B) (hk : k < J)
    (hH : 0 < H) (hR : 0 < R) (hμ : 0 ≤ μ)
    (hbal : Balanced Finset.univ (T.ancestor (k + 1)) R)
    (hparents : μ * (T.layer J).card ≤
      (Finset.univ.filter (fun i => T.ancestor k i ∈ G.parents)).card) :
    (H * μ / R) * (T.layer J).card ≤
      (Finset.univ.filter (fun i => T.ancestor (k + 1) i ∈ G.selected)).card := by
  classical
  let p := T.ancestor (k + 1)
  let w : Fin (T.layer (k + 1)).card → ℝ := fun a => (Finset.univ.filter fun i => p i = a).card
  have hf (i : Fin (T.layer J).card) :
      (Finset.univ.filter fun a => p a = p i) = leafFiber Finset.univ (T.ancestor (k + 1)) i := by
    ext a
    simp [p, leafFiber]
  have hwcomp (a b) : w a ≤ R * w b := by
    obtain ⟨i, rfl⟩ := T.active (k + 1) (by omega) a
    obtain ⟨j, rfl⟩ := T.active (k + 1) (by omega) b
    change ((Finset.univ.filter fun a => p a = p i).card : ℝ) ≤
      R * (Finset.univ.filter fun a => p a = p j).card
    rw [hf i, hf j]
    exact hbal i (Finset.mem_univ _) j (Finset.mem_univ _)
  have hloc (a) (ha : a ∈ G.parents) :
      H * (∑ b ∈ Finset.univ.filter (fun i => T.parent k i = a), w b) ≤
        R * ∑ b ∈ G.selected.filter (fun i => T.parent k i = a), w b := by
    apply weighted_card_retention _ _ _ hR.le hH.le
    · apply Finset.card_pos.mp
      apply (Nat.cast_pos (α := ℝ)).mp
      apply lt_of_lt_of_le _ (G.retained a ha)
      apply mul_pos hH
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr (by
        obtain ⟨b, hb⟩ := T.parent_surjective hk a
        exact ⟨b, by simp [hb]⟩))
    · intro b hb
      exact Nat.cast_nonneg _
    · intro b hb c hc
      exact hwcomp b c
    · exact G.retained a ha
  have hfull : (∑ a ∈ G.parents, ∑ b ∈ Finset.univ.filter (fun i => T.parent k i = a), w b) =
      ((Finset.univ.filter (fun i => T.ancestor k i ∈ G.parents)).card : ℝ) := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    rw [← card_preimage_eq_sum]
    apply congrArg (fun S : Finset (Fin (T.layer J).card) => (S.card : ℝ))
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, p, T.coherent k hk]
  have hsel : (∑ a ∈ G.parents, ∑ b ∈ G.selected.filter (fun i => T.parent k i = a), w b) =
      ((Finset.univ.filter (fun i => p i ∈ G.selected)).card : ℝ) := by
    rw [Finset.sum_fiberwise_of_maps_to G.selected_parent, ← card_preimage_eq_sum]
  have hh := Finset.sum_le_sum hloc
  rw [← Finset.mul_sum, ← Finset.mul_sum, hfull, hsel] at hh
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hR).mpr
  simpa only [mul_assoc, mul_comm R] using (mul_le_mul_of_nonneg_left hparents hH.le).trans hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
