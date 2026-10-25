-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_subtube_selection.Reindex.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_subtube_selection.Geometry
import Submission.WZ.Obl.wz_essentially_distinct_tube_count

/-!
# Re-indexing a family supported on a finset

A family indexed by `Fin n` that vanishes off a finset `F` is re-indexed by `Fin F.card`;
sums and incidence counts are unchanged. Through this, the accepted tube count o043
(`n δ⁶ ≤ C`) bounds `#F` for an essentially distinct fibre inside a coarse tube.
-/

namespace WangZahlLot.Obl.wz_coarse_subtube_selection

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- The enumeration of a finset of `Fin n` by `Fin F.card`. -/
noncomputable def reindex {n : ℕ} (F : Finset (Fin n)) (k : Fin F.card) : Fin n := (F.equivFin.symm k : Fin n)

theorem reindex_injective {n : ℕ} (F : Finset (Fin n)) : Function.Injective (reindex F) :=
  Subtype.val_injective.comp F.equivFin.symm.injective

theorem reindex_mem {n : ℕ} (F : Finset (Fin n)) (k : Fin F.card) : reindex F k ∈ F :=
  (F.equivFin.symm k).2

theorem exists_reindex_eq {n : ℕ} {F : Finset (Fin n)} {i : Fin n} (hi : i ∈ F) :
    ∃ k, reindex F k = i :=
  ⟨F.equivFin ⟨i, hi⟩, by simp [reindex]⟩

theorem sum_reindex {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Finset (Fin n)) (g : Fin n → M) :
    ∑ k, g (reindex F k) = ∑ i ∈ F, g i := by
  rw [← Finset.sum_coe_sort F g]
  exact Fintype.sum_equiv F.equivFin.symm _ _ (fun _ => rfl)

theorem ncard_reindex {n : ℕ} {F : Finset (Fin n)} {P : Fin n → Prop}
    (hP : ∀ i, P i → i ∈ F) :
    {k : Fin F.card | P (reindex F k)}.ncard = {i | P i}.ncard := by
  rw [← Set.ncard_image_of_injective _ (reindex_injective F)]
  congr 1
  ext i
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro hi
    obtain ⟨k, rfl⟩ := exists_reindex_eq (hP i hi)
    exact ⟨k, hi, rfl⟩

/-- An essentially distinct fibre of unit `δ`-tubes inside `T (ρ/2) y w` has at most `C δ⁻⁶`
tubes (o043 after re-indexing and translating the midpoint of `[y, y + w]` to `0`). -/
theorem fibre_card_le : ∃ C : ℝ, 0 < C ∧ ∀ {δ ρ : ℝ}, 0 < δ → δ ≤ 1 / 100 → ρ ≤ 1 →
    ∀ {n : ℕ} (x v : Fin n → Space) (F : Finset (Fin n)) (y w : Space), ‖w‖ = 1 →
    (∀ i ∈ F, ‖v i‖ = 1 ∧ thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      thickening (ρ / 2) (segment ℝ y (y + w))) →
    (∀ i j, i ≠ j → volume (thickening δ (segment ℝ (x i) (x i + v i)) ∩
      thickening δ (segment ℝ (x j) (x j + v j))) ≤
        1 / 2 * volume (thickening δ (segment ℝ (x i) (x i + v i)))) →
    (F.card : ℝ) * δ ^ 6 ≤ C := by
  obtain ⟨C, hC, hcount⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  refine ⟨C, hC, ?_⟩
  intro δ ρ hδ hδ1 hρ1 n x v F y w hw hF hX
  let c : Space := y + (1 / 2 : ℝ) • w
  let x' : Fin F.card → Space := fun k => x (reindex F k) - c
  let v' : Fin F.card → Space := fun k => v (reindex F k)
  refine hcount δ hδ hδ1 F.card x' v' (fun k => (hF _ (reindex_mem F k)).1)
    (fun k => translated_tube_subset_ball hρ1 hw (hF _ (reindex_mem F k)).2) ?_
  intro k l hkl
  simp only [x', v', tube_sub_translate]
  rw [← Set.preimage_inter, measure_preimage_add, measure_preimage_add]
  exact hX _ _ (fun h => hkl (reindex_injective F h))

end WangZahlLot.Obl.wz_coarse_subtube_selection
