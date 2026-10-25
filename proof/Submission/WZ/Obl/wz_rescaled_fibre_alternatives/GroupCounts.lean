-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.GroupCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.Basic

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

/-- Balanced fibre sizes convert an incidence count into a count of cover vertices. -/
lemma balanced_incidence_count {m n N : ℕ} (S : Finset (Fin m)) (f : Fin m → Fin N)
    (j : Fin m → Fin n) (hj : Function.Injective j) {B : ℝ} (hB : 0 ≤ B)
    (hbal : ∀ k l, ((S.filter (fun i => f i = k)).card : ℝ) ≤
      B * (S.filter (fun i => f i = l)).card)
    (Q : Fin N → Prop) (P : Fin n → Prop)
    (hinc : ∀ i ∈ S, Q (f i) → P (j i)) :
    ({k | Q k}.ncard : ℝ) * S.card ≤ B * N * {i | P i}.ncard := by
  classical
  let I := Finset.univ.filter Q
  let a : Fin N → ℝ := fun k => (S.filter (fun i => f i = k)).card
  have hsum : ∑ k, a k = (S.card : ℝ) := by
    dsimp [a]
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hlow (l : Fin N) : (S.card : ℝ) ≤ B * N * a l := by
    rw [← hsum]
    calc
      _ ≤ ∑ _k : Fin N, B * a l := Finset.sum_le_sum (fun k _ => hbal k l)
      _ = _ := by simp; ring
  have hcount : (S.filter (fun i => f i ∈ I)).card ≤ {i | P i}.ncard := by
    apply (show (S.filter (fun i => f i ∈ I)).card =
      ((S.filter (fun i => f i ∈ I)) : Set (Fin m)).ncard by exact (Set.ncard_coe_finset _).symm).trans_le
    apply Set.ncard_le_ncard_of_injOn j
    · intro i hi
      exact hinc i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2
    · exact hj.injOn
  have hIsum : ∑ k ∈ I, a k = ((S.filter (fun i => f i ∈ I)).card : ℝ) := by
    dsimp [a]
    rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]
  have hI : I.card = {k | Q k}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext k
    simp [I]
  rw [← hI]
  calc
    (I.card : ℝ) * S.card = ∑ _k ∈ I, (S.card : ℝ) := by simp
    _ ≤ ∑ k ∈ I, B * N * a k := Finset.sum_le_sum (fun k _ => hlow k)
    _ = B * N * (∑ k ∈ I, a k) := by rw [Finset.mul_sum]
    _ ≤ B * N * {i | P i}.ncard := by
      rw [hIsum]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcount) (by positivity)

/-- The union in each balanced occupied group inherits the parent's slab count. -/
lemma grouped_slabBound {m n N : ℕ} (hn : 0 < n)
    (S : Finset (Fin m)) (f : Fin m → Fin N) (j : Fin m → Fin n)
    (hj : Function.Injective j) {B H L : ℝ} (hB : 0 ≤ B) (hH : 0 < H) (hL : 0 ≤ L)
    (hret : H * n ≤ S.card)
    (hbal : ∀ k l, ((S.filter (fun i => f i = k)).card : ℝ) ≤
      B * (S.filter (fun i => f i = l)).card)
    {D : Set Space} (U : Fin n → Set Space)
    (hSb : SlabBound D L (fun _ => True) U) :
    SlabBound D (B * L / H) (fun _ => True)
      (fun k => ⋃ i ∈ S, ⋃ (_ : f i = k), U (j i)) := by
  classical
  intro u t r hu hr
  let V := fun k => ⋃ i ∈ S, ⋃ (_ : f i = k), U (j i)
  let Q := fun k => V k ⊆ D ∩ slab u t r
  let P := fun i => U i ⊆ D ∩ slab u t r
  have hc := balanced_incidence_count S f j hj hB hbal Q P (by
    intro i hi hq p hp
    exact hq (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, mem_iUnion.mpr ⟨rfl, hp⟩⟩⟩))
  have hcount : ({k | Q k}.ncard : ℝ) * (H * n) ≤ B * N * {i | P i}.ncard :=
    (mul_le_mul_of_nonneg_left hret (Nat.cast_nonneg _)).trans hc
  have hs := hSb u t r hu hr
  simp only [true_and, ofPred_true, ncard_univ, Nat.card_fin] at hs ⊢
  change ENNReal.ofReal ({k | Q k}.ncard : ℝ) * volume D ≤
    ENNReal.ofReal (B * L / H * N) * volume (D ∩ slab u t r)
  have hHn : 0 < H * (n : ℝ) := mul_pos hH (Nat.cast_pos.mpr hn)
  have he₀ : ENNReal.ofReal (H * (n : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr hHn).ne'
  have hmain : ENNReal.ofReal (H * (n : ℝ)) *
      (ENNReal.ofReal ({k | Q k}.ncard : ℝ) * volume D) ≤
      ENNReal.ofReal (H * (n : ℝ)) *
        (ENNReal.ofReal (B * L / H * N) * volume (D ∩ slab u t r)) := by
    calc
      _ = ENNReal.ofReal (({k | Q k}.ncard : ℝ) * (H * n)) * volume D := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        ac_rfl
      _ ≤ ENNReal.ofReal (B * N * {i | P i}.ncard) * volume D :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hcount) _
      _ = ENNReal.ofReal (B * N) * (ENNReal.ofReal ({i | P i}.ncard : ℝ) * volume D) := by
        rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal (B * N) * (ENNReal.ofReal (L * n) * volume (D ∩ slab u t r)) :=
        mul_le_mul_right hs _
      _ = _ := by
        have he : B * (N : ℝ) * (L * n) = (H * n) * (B * L / H * N) := by
          field_simp
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), he,
          ENNReal.ofReal_mul hHn.le, mul_assoc]
  calc
    _ = (ENNReal.ofReal (H * (n : ℝ)))⁻¹ *
        (ENNReal.ofReal (H * (n : ℝ)) * (ENNReal.ofReal ({k | Q k}.ncard : ℝ) * volume D)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel he₀ ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal (H * (n : ℝ)))⁻¹ *
        (ENNReal.ofReal (H * (n : ℝ)) * (ENNReal.ofReal (B * L / H * N) * volume (D ∩ slab u t r))) :=
      mul_le_mul_right hmain _
    _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel he₀ ENNReal.ofReal_ne_top, one_mul]

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
