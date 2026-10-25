-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Partition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open scoped Classical

/-- Replace any finite collection of labels by a surjective map to a finite ordinal. -/
theorem finite_label_map {n : ℕ} {L : Type*} (label : Fin n → L) :
    ∃ m : ℕ, ∃ g : Fin n → Fin m, Function.Surjective g ∧
      ∀ i j, g i = g j ↔ label i = label j := by
  classical
  let C : Finset L := Finset.univ.image label
  let e := Fintype.equivFin C
  let g : Fin n → Fin (Fintype.card C) := fun i => e ⟨label i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  refine ⟨Fintype.card C, g, ?_, ?_⟩
  · intro j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (e.symm j).property
    refine ⟨i, ?_⟩
    change e ⟨label i, _⟩ = j
    rw [← e.apply_symm_apply j]
    congr 1
    exact Subtype.ext hi
  · intro i j
    change e ⟨label i, _⟩ = e ⟨label j, _⟩ ↔ label i = label j
    rw [e.injective.eq_iff, Subtype.mk.injEq]

/-- Every nonempty fibre has a point with maximal weight. -/
theorem choose_fibre_max {I J : Type*} [Fintype I] (g : I → J) (hg : Function.Surjective g)
    (weight : I → ℝ) :
    ∃ a : J → I, (∀ j, g (a j) = j) ∧ ∀ i, weight i ≤ weight (a (g i)) := by
  classical
  have hex : ∀ j, ∃ a, g a = j ∧ ∀ i, g i = j → weight i ≤ weight a := by
    intro j
    obtain ⟨i, hi⟩ := hg j
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => g i = j) weight
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    exact ⟨a, (Finset.mem_filter.mp ha).2,
      fun i hi => hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)⟩
  choose a ha hmax using hex
  exact ⟨a, ha, fun i => hmax (g i) i rfl⟩

theorem sum_fibres {I J A : Type*} [Fintype I] [Fintype J] [AddCommMonoid A]
    (g : I → J) (weight : I → A) :
    (∑ j, ∑ i ∈ Finset.univ.filter (fun i => g i = j), weight i) = ∑ i, weight i := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

noncomputable def enumerate {I : Type*} (S : Finset I) (j : Fin S.card) : I :=
  (S.equivFin.symm j).val

theorem enumerate_mem {I : Type*} (S : Finset I) (j : Fin S.card) : enumerate S j ∈ S :=
  (S.equivFin.symm j).property

theorem enumerate_injective {I : Type*} (S : Finset I) : Function.Injective (enumerate S) :=
  Subtype.val_injective.comp S.equivFin.symm.injective

theorem sum_enumerate {I A : Type*} [AddCommMonoid A] (S : Finset I) (f : I → A) :
    (∑ j : Fin S.card, f (enumerate S j)) = ∑ i ∈ S, f i := by
  rw [← Finset.sum_coe_sort S f]
  exact Equiv.sum_comp S.equivFin.symm (fun i : S => f i)

theorem disjoint_groups_count_le {n m M : ℕ} (A : Fin m → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (hM : ∀ j, M ≤ (A j).card) :
    M * m ≤ n := by
  classical
  calc
    _ = ∑ _j : Fin m, M := by simp [Nat.mul_comm]
    _ ≤ ∑ j, (A j).card := Finset.sum_le_sum (fun j _ => hM j)
    _ = (Finset.univ.biUnion A).card := (Finset.card_biUnion (fun i _ j _ hij => hA hij)).symm
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

end WangZahlLot.Obl.wz_normalized_projection_iteration
