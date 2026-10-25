-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.FibreHalf.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/FibreHalf.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.ClearCore
import Submission.WZ.Obl.wz_broad_grains_initialization.PointwiseRefinement

/-!
Ported (namespace and imports adjusted) from the o169 file
`WangZahlLot/Obl/wz_move_three_wide_grains_core/FibreHalf.lean`, branch x0641 of the o169
repository (sessions x0551/x0556/x0587/x0641/x0661/x0670; workspace code, not accepted).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

open MeasureTheory Set

/-- The pointwise half-refinement can be performed separately in each assigned
fibre, with a total cost independent of the number of fibres. -/
theorem fibrewise_half_refinement {n N : ℕ} (f : Fin n → Fin N)
    (Y U : Fin n → Set V) (hY : ∀ i, MeasurableSet (Y i))
    (hU : ∀ i, MeasurableSet (U i)) (hUY : ∀ i, U i ⊆ Y i) :
    ∃ D : Fin N → Set V, (∀ k, MeasurableSet (D k)) ∧
      (∑ i, μ (Y i)) ≤ (∑ i, μ (U i ∩ D (f i))) + 2 * ∑ i, μ (Y i \ U i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ U i ∩ D (f i)) →
        q n {i | f i = k ∧ p ∈ Y i} ≤
          2 * q n {i | f i = k ∧ p ∈ U i ∩ D (f i)} := by
  classical
  let Yk (k : Fin N) (i : Fin n) := if f i = k then Y i else ∅
  let Uk (k : Fin N) (i : Fin n) := if f i = k then U i else ∅
  have hYk (k : Fin N) (i : Fin n) : MeasurableSet (Yk k i) := by
    dsimp [Yk]
    split_ifs <;> first | exact hY i | exact MeasurableSet.empty
  have hUk (k : Fin N) (i : Fin n) : MeasurableSet (Uk k i) := by
    dsimp [Uk]
    split_ifs <;> first | exact hU i | exact MeasurableSet.empty
  have hsub (k : Fin N) (i : Fin n) : Uk k i ⊆ Yk k i := by
    dsimp [Uk, Yk]
    split_ifs <;> first | exact hUY i | exact Subset.rfl
  have H (k : Fin N) := WangZahlLot.Obl.wz_broad_grains_initialization.pointwise_half_refinement
    (Yk k) (Uk k) (hYk k) (hUk k) (hsub k)
  choose D hDm hmass hcount using H
  refine ⟨D, hDm, ?_, ?_⟩
  · have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hmass k)
    have hleft : (∑ k, ∑ i, μ (Yk k i)) = ∑ i, μ (Y i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Yk, apply_ite μ]
      simp [μ, eq_comm]
    have hright : (∑ k, ∑ i, μ (Uk k i ∩ D k)) = ∑ i, μ (U i ∩ D (f i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have he (k : Fin N) : μ (Uk k i ∩ D k) =
          if f i = k then μ (U i ∩ D k) else 0 := by
        by_cases hi : f i = k <;> simp [Uk, hi, μ]
      simp only [he]
      simp [eq_comm]
    have hdiff : (∑ k, ∑ i, μ (Yk k i \ Uk k i)) = ∑ i, μ (Y i \ U i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have he (k : Fin N) : μ (Yk k i \ Uk k i) =
          if f i = k then μ (Y i \ U i) else 0 := by
        by_cases hi : f i = k <;> simp [Yk, Uk, hi, μ]
      simp only [he]
      simp [eq_comm]
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hleft, hright, hdiff] using hsum
  · intro k p hp
    obtain ⟨i, hi, hpU, hpD⟩ := hp
    have hpk : p ∈ ⋃ i, Uk k i ∩ D k :=
      mem_iUnion.mpr ⟨i, by simpa [Uk, hi] using And.intro hpU (hi ▸ hpD)⟩
    have h := hcount k p hpk
    have heY : {i | p ∈ Yk k i} = {i | f i = k ∧ p ∈ Y i} := by
      ext i
      by_cases hi : f i = k <;> simp [Yk, hi]
    have heU : {i | p ∈ Uk k i ∩ D k} = {i | f i = k ∧ p ∈ U i ∩ D (f i)} := by
      ext i
      by_cases hi : f i = k <;> simp [Uk, hi]
    change q n {i | p ∈ Yk k i} ≤ 2 * q n {i | p ∈ Uk k i ∩ D k} at h
    rwa [heY, heU] at h

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
