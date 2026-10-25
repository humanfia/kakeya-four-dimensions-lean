-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Selection.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Basic
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate
import Submission.WZ.Obl.wz_separated_cover_refinement

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open scoped ENNReal

/-- Geometric pigeonholing makes group sizes uniform and keeps a single color. -/
theorem select_uniform_colored_groups {I : Type*} [Fintype I] {n K : ℕ} (hK : 0 < K)
    (count : I → ℕ) (hcount : ∀ i, 0 < count i ∧ count i ≤ n)
    (color : I → Fin K) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hmass : 0 < ∑ i, weight i) {τ : ℝ} (hτ : 0 < τ) :
    ∃ M : ℕ, 0 < M ∧ ∃ S : Finset I, S.Nonempty ∧
      (∀ i ∈ S, M ≤ count i ∧ count i < 2 * M) ∧
      (∀ i ∈ S, ∀ j ∈ S, color i = color j) ∧
      (∑ i, weight i) * ((1 - (2 : ℝ) ^ (-τ)) / 2) * (n : ℝ) ^ (-τ) ≤
        (K : ℝ) * ∑ i ∈ S, weight i := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  let q : ℝ := (2 : ℝ) ^ (-τ)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hcoef : 0 < (1 - q) / 2 := by linarith
  let mass : ℕ → ℝ≥0∞ := fun k => ∑ i, if Nat.log 2 (count i) = k then ENNReal.ofReal (weight i) else 0
  have hmass_sum : (∑' k, mass k) = ENNReal.ofReal (∑ i, weight i) := by
    calc
      _ = ∑' k, ∑' i, if Nat.log 2 (count i) = k then ENNReal.ofReal (weight i) else 0 := by
        congr 1
        funext k
        exact (tsum_fintype _).symm
      _ = ∑' i, ∑' k, if Nat.log 2 (count i) = k then ENNReal.ofReal (weight i) else 0 :=
        ENNReal.tsum_comm
      _ = ∑ i, ENNReal.ofReal (weight i) := by simp
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)).symm
  obtain ⟨k, hk⟩ := WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_geometric_mass
    hmass hq0.le hq1 hmass_sum.ge
  have hclass : (∑ i, weight i) * ((1 - q) / 2) * q ^ k ≤
      ∑ i, if Nat.log 2 (count i) = k then weight i else 0 := by
    have hnon : ∀ i, 0 ≤ if Nat.log 2 (count i) = k then weight i else 0 := fun i => by
      split_ifs
      · exact hw i
      · exact le_rfl
    apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun i _ => hnon i))).mp
    convert hk using 1
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnon i)]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [mass]
  obtain ⟨d, hd⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.heavy_fibre color
    (fun i => if Nat.log 2 (count i) = k then weight i else 0)
  let S : Finset I := Finset.univ.filter fun i => Nat.log 2 (count i) = k ∧ color i = d
  have hd' : (∑ i, if Nat.log 2 (count i) = k then weight i else 0) ≤
      (K : ℝ) * ∑ i ∈ S, weight i := by
    calc
      _ ≤ _ := hd
      _ = _ := by
        rw [Fintype.card_fin]
        congr 1
        simp only [S, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hl : Nat.log 2 (count i) = k <;> by_cases hc : color i = d <;> simp [hl, hc]
  have hpos : 0 < (∑ i, weight i) * ((1 - q) / 2) * q ^ k := by positivity
  have hS : S.Nonempty := by
    by_contra hn
    have hs : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := hclass.trans hd'
    rw [hs] at hh
    simp only [Finset.sum_empty, mul_zero] at hh
    exact (not_le_of_gt hpos) hh
  let M : ℕ := 2 ^ k
  have hM : 0 < M := by dsimp [M]; positivity
  have hbound : ∀ i ∈ S, M ≤ count i ∧ count i < 2 * M := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2.1
    have hlow := Nat.pow_log_le_self 2 (hcount i).1.ne'
    have hhigh := (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) (hcount i).1.ne').mp
      (Nat.lt_succ_self (Nat.log 2 (count i)))
    rw [hi'] at hlow hhigh
    exact ⟨hlow, by simpa [M, pow_succ, Nat.mul_comm] using hhigh⟩
  have hMn : M ≤ n := by
    obtain ⟨i, hi⟩ := hS
    exact (hbound i hi).1.trans (hcount i).2
  have hqpow : (n : ℝ) ^ (-τ) ≤ q ^ k := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hle : (M : ℝ) ≤ n := by exact_mod_cast hMn
    have hh := Real.rpow_le_rpow_of_nonpos hMr hle (by linarith : -τ ≤ 0)
    simpa only [M, Nat.cast_pow, Nat.cast_ofNat, q, Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)] using hh
  refine ⟨M, hM, S, hS, hbound, ?_, ?_⟩
  · intro i hi j hj
    exact (Finset.mem_filter.mp hi).2.2.trans (Finset.mem_filter.mp hj).2.2.symm
  · exact (mul_le_mul_of_nonneg_left hqpow (by positivity)).trans (hclass.trans hd')

end WangZahlLot.Obl.wz_normalized_projection_iteration
