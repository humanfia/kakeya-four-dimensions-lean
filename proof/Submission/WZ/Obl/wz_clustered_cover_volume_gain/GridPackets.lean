-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GridPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FinitePartition

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set

lemma partition_image_card {n N : ℕ} {κ : Type*} [DecidableEq κ]
    (code : Fin n → κ) (f : Fin n → Fin N) (ref : Fin N → Fin n)
    (href : ∀ k, f (ref k) = k)
    (heq : ∀ i j, f i = f j ↔ code i = code j) (S : Finset (Fin n)) :
    (S.image f).card = (S.image code).card := by
  classical
  have hinj : Function.Injective (fun k => code (ref k)) := by
    intro k l h
    simpa only [href] using (heq (ref k) (ref l)).mpr h
  have he (i : Fin n) : code (ref (f i)) = code i :=
    (heq _ _).mp (href _)
  calc
    _ = ((S.image f).image (fun k => code (ref k))).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = _ := by simp only [Finset.image_image, Function.comp_def, he]

lemma pair_image_card_le {ι κ ν : Type*} [DecidableEq κ] [DecidableEq ν]
    (S : Finset ι) (f : ι → κ) (g : ι → ν) {B : ℕ}
    (hfiber : ∀ k ∈ S.image f, ((S.filter fun i => f i = k).image g).card ≤ B) :
    (S.image fun i => (f i, g i)).card ≤ (S.image f).card * B := by
  classical
  let parts := fun k => ((S.filter fun i => f i = k).image g).image (Prod.mk k)
  have hsub : S.image (fun i => (f i, g i)) ⊆ (S.image f).biUnion parts := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_biUnion.mpr ⟨f i, Finset.mem_image_of_mem f hi, ?_⟩
    exact Finset.mem_image.mpr ⟨g i,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩, rfl⟩
  calc
    _ ≤ ((S.image f).biUnion parts).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ S.image f, (parts k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ S.image f, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.card_image_le.trans (hfiber k hk)
    _ = _ := by simp

/-- Projective caps produce at most twice the grid-cell bound for an ordinary
cap; no choice of a continuous orientation is needed. -/
theorem grid_image_card_le_two {n d A : ℕ} (S : Finset (Fin n))
    (x : Fin n → Fin d → ℝ) (y : Fin d → ℝ) (s : Fin d → ℝ)
    (hs : ∀ j, 0 < s j)
    (hx : ∀ i ∈ S, (∀ j, |x i j - y j| ≤ A * s j) ∨
      (∀ j, |x i j + y j| ≤ A * s j)) :
    (S.image (fun i j => ⌊x i j / s j⌋)).card ≤ 2 * (2 * (A + 1) + 1) ^ d := by
  classical
  let S₀ := S.filter fun i => ∀ j, |x i j - y j| ≤ A * s j
  let S₁ := S.filter fun i => ∀ j, |x i j + y j| ≤ A * s j
  let code := fun i j => ⌊x i j / s j⌋
  have hsub : S ⊆ S₀ ∪ S₁ := by
    intro i hi
    rcases hx i hi with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi, h⟩)
  have h₀ := grid_image_card_le S₀ x y s hs (fun i hi => (Finset.mem_filter.mp hi).2)
  have h₁ := grid_image_card_le S₁ x (fun j => -y j) s hs
    (fun i hi j => by simpa only [sub_neg_eq_add] using (Finset.mem_filter.mp hi).2 j)
  calc
    _ ≤ ((S₀ ∪ S₁).image code).card := Finset.card_le_card (Finset.image_subset_image hsub)
    _ ≤ (S₀.image code).card + (S₁.image code).card := by
      rw [Finset.image_union]
      exact Finset.card_union_le _ _
    _ ≤ _ := by dsimp only [code] at *; omega

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
