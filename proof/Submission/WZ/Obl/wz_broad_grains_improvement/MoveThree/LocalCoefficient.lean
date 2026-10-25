-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.LocalCoefficient.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/LocalCoefficient.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Coefficient

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization
  (count count_le_card Upper coefficient coefficient_le coefficient_upper exists_dense_test)

noncomputable section

attribute [local instance] Classical.propDecidable

variable {κ : Type*} [DecidableEq κ]

/-- The largest convex-count coefficient among the neighborhoods of selected
indices. The floor at one also defines it for the empty family. -/
def localCoefficient (U : κ → Set V) (vol : ℝ) (near : κ → κ → Prop)
    (Q : Finset κ) : ℝ := by
  classical
  exact (insert 1 (Q.image fun j => coefficient U vol (Q.filter (near j)))).max'
    (Finset.insert_nonempty _ _)

theorem one_le_localCoefficient (U : κ → Set V) (vol : ℝ)
    (near : κ → κ → Prop) (Q : Finset κ) :
    1 ≤ localCoefficient U vol near Q := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem coefficient_le_localCoefficient (U : κ → Set V) (vol : ℝ)
    (near : κ → κ → Prop) (Q : Finset κ) (j : κ) (hj : j ∈ Q) :
    coefficient U vol (Q.filter (near j)) ≤ localCoefficient U vol near Q := by
  classical
  unfold localCoefficient
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

/-- A lower volume bound on every body bounds its convex-count coefficient by
the number of bodies, regardless of their overlap. -/
theorem common_volume_upper (U : κ → Set V) (S : Finset κ) {vol : ℝ}
    (hvol : 0 ≤ vol) (hU : ∀ i ∈ S, O vol ≤ μ (U i)) :
    Upper U vol S S.card := by
  classical
  intro W _
  by_cases hz : count U S W = 0
  · simp [hz]
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
  have hUW : U i ⊆ W := (Finset.mem_filter.mp hi).2
  calc
    O ((count U S W : ℝ) * vol) ≤ O (S.card * vol) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (count_le_card U S W)) hvol)
    _ = O (S.card : ℝ) * O vol := ENNReal.ofReal_mul (Nat.cast_nonneg _)
    _ ≤ O (S.card : ℝ) * μ W :=
      mul_le_mul' le_rfl ((hU i hiS).trans (measure_mono hUW))

theorem localCoefficient_le (U : κ → Set V) {vol c : ℝ}
    (near : κ → κ → Prop) (Q : Finset κ) (hc : 1 ≤ c)
    (hU : ∀ j ∈ Q, Upper U vol (Q.filter (near j)) c) :
    localCoefficient U vol near Q ≤ c := by
  classical
  apply Finset.max'_le
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact hc
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    exact coefficient_le hc (hU j hj)

theorem localCoefficient_le_card (U : κ → Set V) {vol : ℝ}
    (near : κ → κ → Prop) (Q : Finset κ) (hvol : 0 ≤ vol)
    (hU : ∀ i ∈ Q, O vol ≤ μ (U i)) :
    localCoefficient U vol near Q ≤ max 1 (Q.card : ℝ) := by
  classical
  apply localCoefficient_le U near Q (le_max_left _ _)
  intro j _
  apply (common_volume_upper U (Q.filter (near j)) hvol
    (fun i hi => hU i (Finset.mem_filter.mp hi).1)).mono
  exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (le_max_right _ _)

theorem localCoefficient_upper (U : κ → Set V) {vol : ℝ}
    (near : κ → κ → Prop) (Q : Finset κ) (hvol : 0 ≤ vol)
    (hU : ∀ i ∈ Q, O vol ≤ μ (U i)) :
    ∀ j ∈ Q, Upper U vol (Q.filter (near j)) (localCoefficient U vol near Q) := by
  classical
  intro j hj
  have hupper : Upper U vol (Q.filter (near j)) (max 1 (Q.card : ℝ)) := by
    apply (common_volume_upper U (Q.filter (near j)) hvol
      (fun i hi => hU i (Finset.mem_filter.mp hi).1)).mono
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (le_max_right _ _)
  exact (coefficient_upper hvol (le_max_left _ _) hupper).mono
    (coefficient_le_localCoefficient U vol near Q j hj)

/-- Above the floor, the local coefficient is attained at one selected
neighborhood, which in turn has an almost maximizing convex test set. -/
theorem localCoefficient_dense_test (U : κ → Set V) {vol : ℝ}
    (near : κ → κ → Prop) (Q : Finset κ) (hvol : 0 ≤ vol)
    (hU : ∀ i ∈ Q, O vol ≤ μ (U i))
    (hlarge : 2 < localCoefficient U vol near Q) :
    ∃ j ∈ Q, ∃ W : Set V, Convex ℝ W ∧ μ W ≠ ⊤ ∧
      localCoefficient U vol near Q / 2 * (μ W).toReal <
        (count U (Q.filter (near j)) W : ℝ) * vol := by
  classical
  have hmem := Finset.max'_mem
    (insert 1 (Q.image fun j => coefficient U vol (Q.filter (near j))))
    (Finset.insert_nonempty _ _)
  change localCoefficient U vol near Q ∈ _ at hmem
  rcases Finset.mem_insert.mp hmem with he | he
  · linarith
  · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp he
    have hupper : Upper U vol (Q.filter (near j)) (max 1 (Q.card : ℝ)) := by
      apply (common_volume_upper U (Q.filter (near j)) hvol
        (fun i hi => hU i (Finset.mem_filter.mp hi).1)).mono
      exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (le_max_right _ _)
    obtain ⟨W, hW, hfin, hden⟩ := exists_dense_test hvol (le_max_left _ _) hupper
      (by rwa [he])
    exact ⟨j, hj, W, hW, hfin, by rwa [he] at hden⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
