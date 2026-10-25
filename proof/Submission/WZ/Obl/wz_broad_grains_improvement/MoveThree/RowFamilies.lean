-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.RowFamilies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/RowFamilies.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/RowFamilies.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SubfamilyRefinement

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open Set MeasureTheory
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (extendSets enumerate enumerate_mem enumerate_surj extendSets_enumerate extendSets_outside)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (bodyCount bodyCount_extendSets)

/-- Extension by empty rows preserves every predicate count, including
angular cap counts, exactly. -/
theorem predicate_count_extendSets {L : ℕ} (Q : Finset (Fin L))
    (W : Fin Q.card → Set V) (test : Fin L → Prop) (p : V) :
    q L {j | p ∈ extendSets Q W j ∧ test j} =
      q Q.card {i | p ∈ W i ∧ test (enumerate Q i)} := by
  classical
  let W' := fun i => if test (enumerate Q i) then W i else ∅
  have he : extendSets Q W' = fun j => if test j then extendSets Q W j else ∅ := by
    funext j
    by_cases hj : j ∈ Q
    · obtain ⟨i, rfl⟩ := enumerate_surj Q hj
      rw [extendSets_enumerate, extendSets_enumerate]
    · rw [extendSets_outside Q W' hj, extendSets_outside Q W hj]
      split_ifs <;> rfl
  have hcount := bodyCount_extendSets Q W' p
  rw [he] at hcount
  have hleft : {j | p ∈ if test j then extendSets Q W j else ∅} =
      {j | p ∈ extendSets Q W j ∧ test j} := by
    ext j
    by_cases hj : test j <;> simp [hj]
  have hright : {i | p ∈ W' i} = {i | p ∈ W i ∧ test (enumerate Q i)} := by
    ext i
    by_cases hi : test (enumerate Q i) <;> simp [W', hi]
  change ({j | p ∈ if test j then extendSets Q W j else ∅}.ncard : ℝ) =
    ({i | p ∈ W' i}.ncard : ℝ) at hcount
  simpa only [hleft, hright] using hcount

/-- Extending local rows by empty sets also preserves their spatial union. -/
theorem iUnion_extendSets_univ {L : ℕ} (Q : Finset (Fin L))
    (W : Fin Q.card → Set V) : (⋃ j, extendSets Q W j) = ⋃ i, W i := by
  rw [← WangZahlLot.Obl.wz_regular_transverse_affine_cells.iUnion_extendSets Q W]
  apply Subset.antisymm
  · intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    by_cases hQ : j ∈ Q
    · exact mem_iUnion₂.mpr ⟨j, hQ, hj⟩
    · rw [extendSets_outside _ _ hQ] at hj
      exact hj.elim
  · exact iUnion₂_subset fun j _ => subset_iUnion _ j

/-- Independent refinements of already disjoint parent rows concatenate
without a new loss. The product of their two retention factors is exact. -/
theorem concatenate_row_refinements {κ : Type*} [Fintype κ]
    {Λ : κ → Type*} [∀ k, Fintype (Λ k)] {L : ℕ}
    (H : Fin L → Set V) (U : κ → Fin L → Set V)
    (W : ∀ k, Λ k → Fin L → Set V) {t₀ t₁ : ℝ}
    (ht₀ : 0 ≤ t₀) (_ht₁ : 0 ≤ t₁)
    (hUH : ∀ k j, U k j ⊆ H j)
    (hUdisj : ∀ j, Pairwise fun k k' => Disjoint (U k j) (U k' j))
    (hWm : ∀ k l j, MeasurableSet (W k l j))
    (hWU : ∀ k l j, W k l j ⊆ U k j)
    (hWdisj : ∀ k j, Pairwise fun l l' => Disjoint (W k l j) (W k l' j))
    (hret₀ : O t₀ * ∑ j, μ (H j) ≤ ∑ k, ∑ j, μ (U k j))
    (hret₁ : ∀ k, O t₁ * ∑ j, μ (U k j) ≤ ∑ l, ∑ j, μ (W k l j)) :
    (∀ (a : Sigma Λ) j, MeasurableSet (W a.1 a.2 j) ∧ W a.1 a.2 j ⊆ H j) ∧
      (∀ j, Pairwise fun (a a' : Sigma Λ) => Disjoint (W a.1 a.2 j) (W a'.1 a'.2 j)) ∧
      O (t₀ * t₁) * ∑ j, μ (H j) ≤ ∑ a : Sigma Λ, ∑ j, μ (W a.1 a.2 j) := by
  classical
  refine ⟨fun a j => ⟨hWm a.1 a.2 j, (hWU a.1 a.2 j).trans (hUH a.1 j)⟩, ?_, ?_⟩
  · intro j a a' hne
    obtain ⟨k, l⟩ := a
    obtain ⟨k', l'⟩ := a'
    by_cases hk : k = k'
    · subst k'
      exact hWdisj k j (fun he => hne (congrArg (Sigma.mk k) he))
    · exact (hUdisj j hk).mono (hWU k l j) (hWU k' l' j)
  · calc
      _ = O t₁ * (O t₀ * ∑ j, μ (H j)) := by
        dsimp only [O]
        rw [ENNReal.ofReal_mul ht₀]
        ac_rfl
      _ ≤ O t₁ * ∑ k, ∑ j, μ (U k j) := mul_le_mul' le_rfl hret₀
      _ = ∑ k, O t₁ * ∑ j, μ (U k j) := Finset.mul_sum _ _ _
      _ ≤ ∑ k, ∑ l, ∑ j, μ (W k l j) := Finset.sum_le_sum fun k _ => hret₁ k
      _ = _ := (Fintype.sum_sigma (fun a : Sigma Λ => ∑ j, μ (W a.1 a.2 j))).symm

/-- Within disjoint index blocks, local row refinements remain disjoint
when extended to all the original grains. Their global mass is the sum of
the local masses, by the accepted empty-row extension identities. -/
theorem extend_disjoint_block_rows {κ : Type*} [Fintype κ]
    {Λ : κ → Type*} [∀ k, Fintype (Λ k)] {L : ℕ}
    (Q : κ → Finset (Fin L)) (W : ∀ k, Λ k → Fin (Q k).card → Set V)
    (H : Fin L → Set V)
    (hQ : Pairwise fun k k' => Disjoint (Q k) (Q k'))
    (hWm : ∀ k l i, MeasurableSet (W k l i))
    (hWH : ∀ k l i, W k l i ⊆ H (enumerate (Q k) i))
    (hWdisj : ∀ k i, Pairwise fun l l' => Disjoint (W k l i) (W k l' i)) :
    (∀ (a : Sigma Λ) j, MeasurableSet (extendSets (Q a.1) (W a.1 a.2) j) ∧
      extendSets (Q a.1) (W a.1 a.2) j ⊆ H j) ∧
    (∀ j, Pairwise fun (a a' : Sigma Λ) =>
      Disjoint (extendSets (Q a.1) (W a.1 a.2) j) (extendSets (Q a'.1) (W a'.1 a'.2) j)) ∧
    (∑ a : Sigma Λ, ∑ j, μ (extendSets (Q a.1) (W a.1 a.2) j)) =
      ∑ k, ∑ l, ∑ i, μ (W k l i) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a j
    by_cases hj : j ∈ Q a.1
    · obtain ⟨i, rfl⟩ := enumerate_surj (Q a.1) hj
      rw [extendSets_enumerate]
      exact ⟨hWm a.1 a.2 i, hWH a.1 a.2 i⟩
    · rw [extendSets_outside _ _ hj]
      exact ⟨MeasurableSet.empty, empty_subset _⟩
  · intro j a a' hne
    obtain ⟨k, l⟩ := a
    obtain ⟨k', l'⟩ := a'
    by_cases hk : k = k'
    · subst k'
      by_cases hj : j ∈ Q k
      · obtain ⟨i, rfl⟩ := enumerate_surj (Q k) hj
        simp only [extendSets_enumerate]
        exact hWdisj k i (fun he => hne (congrArg (Sigma.mk k) he))
      · simp only [extendSets_outside _ _ hj, disjoint_empty]
    · by_cases hj : j ∈ Q k
      · have hj' : j ∉ Q k' := fun hj' => Finset.disjoint_left.mp (hQ hk) hj hj'
        rw [extendSets_outside _ _ hj']
        exact disjoint_empty _
      · rw [extendSets_outside _ _ hj]
        exact empty_disjoint _
  · simp_rw [show ∀ (a : Sigma Λ),
      (∑ j, μ (extendSets (Q a.1) (W a.1 a.2) j)) = ∑ i, μ (W a.1 a.2 i) from
        fun a => WangZahlLot.Obl.wz_clustered_cover_volume_gain.sum_extendSets_univ _ _]
    exact Fintype.sum_sigma (fun a : Sigma Λ => ∑ i, μ (W a.1 a.2 i))

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
