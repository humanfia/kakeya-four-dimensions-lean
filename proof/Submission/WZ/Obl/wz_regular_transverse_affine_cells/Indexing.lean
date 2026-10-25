-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Indexing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set

noncomputable def enumerate {ι : Type*} (I : Finset ι) : Fin I.card ↪ ι :=
  I.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)

lemma enumerate_mem {ι : Type*} (I : Finset ι) (j : Fin I.card) : enumerate I j ∈ I :=
  (I.equivFin.symm j).property

lemma enumerate_surj {ι : Type*} (I : Finset ι) {i : ι} (hi : i ∈ I) :
    ∃ j, enumerate I j = i := by
  exact ⟨I.equivFin ⟨i, hi⟩, congrArg Subtype.val (I.equivFin.symm_apply_apply ⟨i, hi⟩)⟩

lemma sum_enumerate {ι M : Type*} [AddCommMonoid M] (I : Finset ι) (f : ι → M) :
    ∑ j, f (enumerate I j) = ∑ i ∈ I, f i := by
  exact (I.equivFin.symm.sum_comp (fun i : I => f i)).trans (Finset.sum_coe_sort I f)

open Classical in
noncomputable def extendSets {ι : Type*} (I : Finset ι) (Y : Fin I.card → Set E) : ι → Set E :=
  fun i => if hi : i ∈ I then Y (I.equivFin ⟨i, hi⟩) else ∅

lemma extendSets_enumerate {ι : Type*} (I : Finset ι) (Y : Fin I.card → Set E)
    (j : Fin I.card) : extendSets I Y (enumerate I j) = Y j := by
  classical
  simp only [extendSets, enumerate_mem, dite_true]
  have he : (⟨enumerate I j, enumerate_mem I j⟩ : I) = I.equivFin.symm j := rfl
  rw [he, I.equivFin.apply_symm_apply]

lemma extendSets_outside {ι : Type*} (I : Finset ι) (Y : Fin I.card → Set E)
    {i : ι} (hi : i ∉ I) : extendSets I Y i = ∅ := by
  classical
  simp only [extendSets, dite_eq_right hi]

lemma sum_extendSets {ι M : Type*} [AddCommMonoid M] (I : Finset ι)
    (Y : Fin I.card → Set E) (f : Set E → M) :
    ∑ i ∈ I, f (extendSets I Y i) = ∑ j, f (Y j) := by
  rw [← sum_enumerate]
  apply Finset.sum_congr rfl
  intro j _
  rw [extendSets_enumerate]

lemma iUnion_extendSets {ι : Type*} (I : Finset ι) (Y : Fin I.card → Set E) :
    (⋃ i ∈ I, extendSets I Y i) = ⋃ j, Y j := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
    obtain ⟨j, rfl⟩ := enumerate_surj I hi
    rw [extendSets_enumerate] at hpi
    exact mem_iUnion.mpr ⟨j, hpi⟩
  · intro hp
    obtain ⟨j, hpj⟩ := mem_iUnion.mp hp
    exact mem_iUnion₂.mpr ⟨enumerate I j, enumerate_mem I j, by rwa [extendSets_enumerate]⟩

/-- A shape palette loses only its cardinality when one color class is retained. -/
lemma exists_large_color_class {ι κ : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    (I : Finset ι) (hI : I.Nonempty) (color : ι → κ) :
    ∃ k : κ, (I.filter fun i => color i = k).Nonempty ∧
      (I.card : ℝ) ≤ Fintype.card κ * ((I.filter fun i => color i = k).card : ℝ) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  obtain ⟨k, _, hk⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := I) (t := Finset.univ) (f := color) (b := (I.card : ℝ) / Fintype.card κ)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by
      rw [nsmul_eq_mul]
      apply le_of_eq
      simp only [Finset.card_univ]
      field_simp)
  refine ⟨k, ?_, ?_⟩
  · apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
    have hf : (0 : ℝ) < (I.filter fun i => color i = k).card :=
      lt_of_lt_of_le (div_pos hpos hcard) hk
    exact_mod_cast hf
  · have h := (div_le_iff₀ hcard).mp hk
    nlinarith

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
