-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.FiniteRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Set

lemma sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α)
    (f : α → List β) (w : β → M) :
    ((L.flatMap f).map w).sum = (L.map fun a => ((f a).map w).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-- Replace each member of a disjoint finite family by a disjoint family inside it.
The support and weight accounting are independent of the geometric construction. -/
lemma refine_finite_list {α β X : Type*} (L : List α) (s : α → Set X) (t : β → Set X)
    (w : α → ℝ) (v : β → ℝ) (Good : β → Prop) (θ : ℝ)
    (hdisj : L.Pairwise (fun a b => Disjoint (s a) (s b)))
    (hrefine : ∀ a ∈ L, ∃ M : List β,
      (∀ b ∈ M, Good b ∧ t b ⊆ s a) ∧
      M.Pairwise (fun a b => Disjoint (t a) (t b)) ∧ θ * w a ≤ (M.map v).sum) :
    ∃ M : List β, (∀ b ∈ M, Good b ∧ ∃ a ∈ L, t b ⊆ s a) ∧
      M.Pairwise (fun a b => Disjoint (t a) (t b)) ∧
      θ * (L.map w).sum ≤ (M.map v).sum := by
  classical
  have hchoose : ∀ a : α, ∃ M : List β, a ∈ L →
      (∀ b ∈ M, Good b ∧ t b ⊆ s a) ∧
      M.Pairwise (fun a b => Disjoint (t a) (t b)) ∧ θ * w a ≤ (M.map v).sum := by
    intro a
    by_cases ha : a ∈ L
    · obtain ⟨M, hM⟩ := hrefine a ha
      exact ⟨M, fun _ => hM⟩
    · exact ⟨[], fun h => False.elim (ha h)⟩
  choose f hf using hchoose
  refine ⟨L.flatMap f, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    exact ⟨((hf a ha).1 b hb).1, a, ha, ((hf a ha).1 b hb).2⟩
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun a ha => (hf a ha).2.1, ?_⟩
    apply List.Pairwise.imp_of_mem ?_ hdisj
    intro a b ha hb hab x hx y hy
    exact hab.mono ((hf a ha).1 x hx).2 ((hf b hb).1 y hy).2
  · rw [sum_map_flatMap, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun a ha => (hf a ha).2.2

/-- Abstract finite-depth extraction. An unresolved node has one fewer refinement
level available, while a terminal node is retained as it is. -/
lemma finite_depth_extraction {α β X : Type*} (N : ℕ)
    (P : ℕ → α → Prop) (Good : β → Prop)
    (s : α → Set X) (t : β → Set X) (w : α → ℝ) (v : β → ℝ)
    (hv : ∀ b, 0 ≤ v b) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hbottom : ∀ a, ¬ P N a)
    (hstep : ∀ j < N, ∀ a, P j a → ∃ L : List (β ⊕ α),
      (∀ z ∈ L, (Sum.elim Good (P (j + 1))) z ∧ (Sum.elim t s) z ⊆ s a) ∧
      L.Pairwise (fun z z' => Disjoint ((Sum.elim t s) z) ((Sum.elim t s) z')) ∧
      q * w a ≤ (L.map (Sum.elim v w)).sum) :
    ∀ a, P 0 a → ∃ M : List β, (∀ b ∈ M, Good b ∧ t b ⊆ s a) ∧
      M.Pairwise (fun a b => Disjoint (t a) (t b)) ∧
      q ^ N * w a ≤ (M.map v).sum := by
  have hind : ∀ k j, j + k = N → ∀ a, P j a →
      ∃ M : List β, (∀ b ∈ M, Good b ∧ t b ⊆ s a) ∧
        M.Pairwise (fun a b => Disjoint (t a) (t b)) ∧
        q ^ k * w a ≤ (M.map v).sum := by
    intro k
    induction k with
    | zero =>
      intro j hj a ha
      have hjN : j = N := by omega
      exact False.elim (hbottom a (hjN ▸ ha))
    | succ k ih =>
      intro j hj a ha
      obtain ⟨L, hL, hLdisj, hLmass⟩ := hstep j (by omega) a ha
      have hrefine : ∀ z ∈ L, ∃ M : List β,
          (∀ b ∈ M, Good b ∧ t b ⊆ (Sum.elim t s) z) ∧
          M.Pairwise (fun a b => Disjoint (t a) (t b)) ∧
          q ^ k * (Sum.elim v w) z ≤ (M.map v).sum := by
        intro z hz
        cases z with
        | inl b =>
          refine ⟨[b], ?_, by simp, ?_⟩
          · intro b' hb'
            have he : b' = b := by simpa using hb'
            subst b'
            exact ⟨(hL _ hz).1, Subset.rfl⟩
          · simpa using mul_le_of_le_one_left (hv b) (pow_le_one₀ hq hq1)
        | inr a' =>
          exact ih (j + 1) (by omega) a' (hL _ hz).1
      obtain ⟨M, hM, hMdisj, hMmass⟩ := refine_finite_list L (Sum.elim t s) t
        (Sum.elim v w) v Good (q ^ k) hLdisj hrefine
      refine ⟨M, ?_, hMdisj, ?_⟩
      · intro b hb
        obtain ⟨hbGood, z, hz, hbsub⟩ := hM b hb
        exact ⟨hbGood, hbsub.trans (hL z hz).2⟩
      · calc q ^ (k + 1) * w a = q ^ k * (q * w a) := by rw [pow_succ]; ring
          _ ≤ q ^ k * (L.map (Sum.elim v w)).sum := mul_le_mul_of_nonneg_left hLmass (pow_nonneg hq _)
          _ ≤ _ := hMmass
  intro a ha
  exact hind N 0 (by omega) a ha

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
