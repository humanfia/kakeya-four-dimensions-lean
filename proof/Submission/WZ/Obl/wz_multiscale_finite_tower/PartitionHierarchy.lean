-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.PartitionHierarchy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Hierarchy

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open WangZahlLot.Obl.wz_tower_balanced_refinement (Balanced leafFiber)

/-- Construct all parent maps from full nested leaf partitions. The terminal
partition need only be a bijection, so inserting levels creates no leaf casts. -/
noncomputable def hierarchyOfPartitions {J n : ℕ} (L : ℕ → Layer)
    (p : ∀ j, Fin n → Fin (L j).card) (hfinal : Function.Bijective (p J))
    (hfull : ∀ j, j ≤ J → Function.Surjective (p j))
    (hnest : ∀ j, j < J → ∀ a b, p (j + 1) a = p (j + 1) b → p j a = p j b) : TubeHierarchy J := by
  classical
  let e : Fin n ≃ Fin (L J).card := Equiv.ofBijective (p J) hfinal
  let f (j : ℕ) (k : Fin (L (j + 1)).card) : Fin (L j).card :=
    if hj : j < J then p j (Classical.choose (hfull (j + 1) (by omega) k)) else ⟨0, (L j).card_pos⟩
  refine ⟨L, f, (fun j => p j ∘ e.symm), ?_, ?_, ?_⟩
  · funext i
    exact e.apply_symm_apply i
  · intro j hj i
    dsimp only [Function.comp_apply, f]
    rw [dif_pos hj]
    exact hnest j hj _ _ (Classical.choose_spec (hfull (j + 1) (by omega) (p (j + 1) (e.symm i))))
  · intro j hj k
    obtain ⟨i, hi⟩ := hfull j hj k
    exact ⟨e i, by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hi⟩

lemma hierarchyOfPartitions_parent {J n : ℕ} (L : ℕ → Layer)
    (p : ∀ j, Fin n → Fin (L j).card) (hfinal : Function.Bijective (p J))
    (hfull : ∀ j, j ≤ J → Function.Surjective (p j))
    (hnest : ∀ j, j < J → ∀ a b, p (j + 1) a = p (j + 1) b → p j a = p j b)
    {j : ℕ} (hj : j < J) (i : Fin n) :
    (hierarchyOfPartitions L p hfinal hfull hnest).parent j (p (j + 1) i) = p j i := by
  classical
  dsimp only [hierarchyOfPartitions]
  rw [dif_pos hj]
  exact hnest j hj _ _ (Classical.choose_spec (hfull (j + 1) (by omega) (p (j + 1) i)))

lemma balanced_comp_equiv {n m k : ℕ} (e : Fin m ≃ Fin n) (p : Fin n → Fin k) {R : ℝ}
    (h : Balanced Finset.univ p R) : Balanced Finset.univ (p ∘ e) R := by
  classical
  have he (i : Fin m) : (leafFiber Finset.univ (p ∘ e) i).card =
      (leafFiber Finset.univ p (e i)).card := by
    have him : e '' (leafFiber Finset.univ (p ∘ e) i : Set (Fin m)) =
        (leafFiber Finset.univ p (e i) : Set (Fin n)) := by
      ext b
      simp only [Set.mem_image, Finset.mem_coe, leafFiber, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.comp_apply]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hb
        exact ⟨e.symm b, by simpa only [Equiv.apply_symm_apply] using hb, e.apply_symm_apply b⟩
    rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ e.injective, him, Set.ncard_coe_finset]
  intro i hi j hj
  rw [he i, he j]
  exact h (e i) (Finset.mem_univ _) (e j) (Finset.mem_univ _)

lemma hierarchyOfPartitions_balanced {J n : ℕ} (L : ℕ → Layer)
    (p : ∀ j, Fin n → Fin (L j).card) (hfinal : Function.Bijective (p J))
    (hfull : ∀ j, j ≤ J → Function.Surjective (p j))
    (hnest : ∀ j, j < J → ∀ a b, p (j + 1) a = p (j + 1) b → p j a = p j b)
    {R : ℝ} {j : ℕ} (h : Balanced Finset.univ (p j) R) :
    Balanced Finset.univ ((hierarchyOfPartitions L p hfinal hfull hnest).ancestor j) R := by
  exact balanced_comp_equiv (Equiv.ofBijective (p J) hfinal).symm (p j) h

end WangZahlLot.Obl.wz_multiscale_finite_tower
