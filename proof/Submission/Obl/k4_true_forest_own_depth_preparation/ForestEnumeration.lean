import Submission.Obl.k4_true_forest_own_depth_preparation.ForestPruning

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open Classical

/-- Enumerate the ancestor-closed survivors without duplicating any label. -/
theorem enumerate_kept {C : ℕ} (lev : Fin C → ℕ) (par : Fin C → Fin C)
    (good : Fin C → Prop) (hpar : ∀ b, 0 < lev b → lev (par b) + 1 = lev b) :
    ∃ (C' : ℕ) (emb : Fin C' ↪ Fin C) (par' : Fin C' → Fin C'),
      C' ≤ C ∧ (∀ b, Kept lev par good (emb b)) ∧
      (∀ b, 0 < lev (emb b) → emb (par' b) = par (emb b)) ∧
      ∀ (mass : Fin C → ENNReal) (i : ℕ),
        (∑ b, if lev b = i ∧ Kept lev par good b then mass b else 0) =
          ∑ b, if lev (emb b) = i then mass (emb b) else 0 := by
  classical
  let I := {b : Fin C // Kept lev par good b}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let emb : Fin (Fintype.card I) ↪ Fin C :=
    e.toEmbedding.trans (Function.Embedding.subtype _)
  have hk (b) : Kept lev par good (emb b) := (e b).property
  let par' (b : Fin (Fintype.card I)) : Fin (Fintype.card I) :=
    if hb : 0 < lev (emb b) then
      e.symm ⟨par (emb b), kept_parent hpar (hk b) hb⟩ else b
  refine ⟨Fintype.card I, emb, par', ?_, hk, ?_, ?_⟩
  · simpa only [I, Fintype.card_fin] using Fintype.card_subtype_le (Kept lev par good)
  · intro b hb
    dsimp only [par']
    rw [dif_pos hb]
    change (e (e.symm ⟨par (emb b), kept_parent hpar (hk b) hb⟩)).val = par (emb b)
    rw [e.apply_symm_apply]
  · intro mass i
    let f : Fin C → ENNReal := fun b => if lev b = i then mass b else 0
    have hs : (∑ b, if lev b = i ∧ Kept lev par good b then mass b else 0) =
        ∑ b : I, f b.val := by
      trans ∑ b ∈ Finset.univ.filter (Kept lev par good), f b
      · rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b _
        by_cases hk : Kept lev par good b <;> simp [hk, f]
      · exact Finset.sum_subtype _ (by simp) f
    rw [hs]
    exact (e.sum_comp (fun b : I => f b.val)).symm

/-- Pull a list back through an injective relabeling. -/
noncomputable def restrictedList {C C' : ℕ} (emb : Fin C' ↪ Fin C)
    (s : Finset (Fin C)) : Finset (Fin C') := by
  classical
  exact Finset.univ.filter (fun b => emb b ∈ s)

theorem restrictedList_card {C C' : ℕ} (emb : Fin C' ↪ Fin C) (s : Finset (Fin C)) :
    (restrictedList emb s).card ≤ s.card := by
  classical
  have hsub : (restrictedList emb s).map emb ⊆ s := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
    exact (Finset.mem_filter.mp ha).2
  simpa only [Finset.card_map] using Finset.card_le_card hsub

end Submission.Obl.k4_true_forest_own_depth_preparation
