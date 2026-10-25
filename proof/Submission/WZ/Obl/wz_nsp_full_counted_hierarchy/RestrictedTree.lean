-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.RestrictedTree.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.BranchBalance
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Counting

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open Set
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- Restrict every layer to the ancestors of a chosen leaf subset. The
enumerations are injective, parent maps commute, and immediate fiber counts
are exactly the occupied branch counts of the leaf partitions. -/
theorem restrict_partition_tower (n : ℕ → ℕ) (J : ℕ)
    (p : ∀ j, Fin (n J) → Fin (n j))
    (f : ∀ j, Fin (n (j + 1)) → Fin (n j))
    (hcoh : ∀ j, j < J → ∀ i, f j (p (j + 1) i) = p j i)
    (S : Finset (Fin (n J))) (hS : S.Nonempty) :
    ∃ (k : ℕ → ℕ) (q : ∀ j, Fin (k j) → Fin (n j))
      (g : ∀ j, Fin (k (j + 1)) → Fin (k j)),
      (∀ j, 0 < k j ∧ Function.Injective (q j) ∧ Set.range (q j) = (S.image (p j) : Set (Fin (n j)))) ∧
      ∀ j, j < J → (∀ t, q j (g j t) = f j (q (j + 1) t)) ∧
        ∀ (t : Fin (k j)) (i : Fin (n J)), i ∈ S → p j i = q j t →
          Set.ncard {s | g j s = t} = (branchFiber S (p j) (p (j + 1)) i).card := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  let V (j : ℕ) := {a : Fin (n j) // a ∈ S.image (p j)}
  let k (j : ℕ) := Fintype.card (V j)
  let e (j : ℕ) : Fin (k j) ≃ V j := (Fintype.equivFin (V j)).symm
  let q (j : ℕ) (i : Fin (k j)) := (e j i).val
  have hqinj (j) : Function.Injective (q j) := Subtype.val_injective.comp (e j).injective
  have hqmem (j) (i : Fin (k j)) : q j i ∈ S.image (p j) := (e j i).property
  have hqrange (j) : Set.range (q j) = (S.image (p j) : Set (Fin (n j))) := by
    ext a
    constructor
    · rintro ⟨t, rfl⟩
      exact hqmem j t
    · intro ha
      exact ⟨(e j).symm ⟨a, ha⟩, congrArg Subtype.val ((e j).apply_symm_apply _)⟩
  have hex (j) (hj : j < J) (t : Fin (k (j + 1))) :
      f j (q (j + 1) t) ∈ S.image (p j) := by
    obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp (hqmem (j + 1) t)
    refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
    rw [← hqa, hcoh j hj]
  let g (j : ℕ) (t : Fin (k (j + 1))) : Fin (k j) :=
    if hj : j < J then (e j).symm ⟨f j (q (j + 1) t), hex j hj t⟩
    else (e j).symm ⟨p j i₀, Finset.mem_image.mpr ⟨i₀, hi₀, rfl⟩⟩
  have hcomm (j) (hj : j < J) (t) : q j (g j t) = f j (q (j + 1) t) := by
    simp only [g, dite_eq_left hj, q, Equiv.apply_symm_apply]
  refine ⟨k, q, g, ?_, ?_⟩
  · intro j
    have hne : Nonempty (V j) := ⟨⟨p j i₀, Finset.mem_image.mpr ⟨i₀, hi₀, rfl⟩⟩⟩
    exact ⟨Fintype.card_pos_iff.mpr hne, hqinj j, hqrange j⟩
  · intro j hj
    refine ⟨hcomm j hj, ?_⟩
    intro t i hi hpi
    have he : q (j + 1) '' {s | g j s = t} =
        (branchFiber S (p j) (p (j + 1)) i : Set (Fin (n (j + 1)))) := by
      ext b
      constructor
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp (hqmem (j + 1) s)
        apply Finset.mem_image.mpr
        refine ⟨a, ?_, hqa⟩
        simp only [leafFiber, Finset.mem_filter]
        refine ⟨ha, ?_⟩
        calc
          p j a = f j (p (j + 1) a) := (hcoh j hj a).symm
          _ = f j (q (j + 1) s) := congrArg (f j) hqa
          _ = q j (g j s) := (hcomm j hj s).symm
          _ = q j t := congrArg (q j) hs
          _ = p j i := hpi.symm
      · intro hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        have ha' : a ∈ S ∧ p j a = p j i := by
          simpa only [leafFiber, Finset.mem_filter] using ha
        obtain ⟨haS, hpa⟩ := ha'
        have hmem : p (j + 1) a ∈ Set.range (q (j + 1)) := by
          rw [hqrange]
          exact Finset.mem_image.mpr ⟨a, haS, rfl⟩
        obtain ⟨s, hs⟩ := hmem
        refine ⟨s, ?_, hs⟩
        apply hqinj j
        rw [hcomm j hj, hs, hcoh j hj, hpa, hpi]
    rw [← Set.ncard_image_of_injective _ (hqinj (j + 1)), he, Set.ncard_coe_finset]

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
