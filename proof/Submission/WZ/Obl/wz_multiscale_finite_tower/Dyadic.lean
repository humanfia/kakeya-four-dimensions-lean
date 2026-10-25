-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Dyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Regularization

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

/-- A finite collection of positive weights contains a factor-two class carrying its average
share of the total mass over the possible dyadic classes. -/
theorem dyadic_weights {ι : Type*} [Fintype ι] {K : ℕ} (w : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hlow : ∀ i, a ≤ w i) (hupp : ∀ i, w i ≤ (2 : ℝ) ^ K * a)
    (hmass : 0 < ∑ i, w i) :
    ∃ k : ℕ, k ≤ K ∧ ∃ S : Finset ι, S.Nonempty ∧
      (∑ i, w i) / (K + 1) ≤ ∑ i ∈ S, w i ∧
      ∀ i ∈ S, (2 : ℝ) ^ k * a ≤ w i ∧ w i < (2 : ℝ) ^ (k + 1) * a := by
  classical
  have hbin : ∀ i, ∃ j : Fin (K + 1),
      (2 : ℝ) ^ (j : ℕ) * a ≤ w i ∧ w i < (2 : ℝ) ^ ((j : ℕ) + 1) * a := by
    intro i
    obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near
      (show 1 ≤ w i / a from (le_div_iff₀ ha).mpr (by simpa using hlow i))
      (show (1 : ℝ) < 2 by norm_num)
    have hjK : j ≤ K := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      (hj.trans ((div_le_iff₀ ha).mpr (hupp i)))
    exact ⟨⟨j, by omega⟩, (le_div_iff₀ ha).mp hj, (div_lt_iff₀ ha).mp hj'⟩
  choose f hf using hbin
  have hK : (0 : ℝ) < K + 1 := by positivity
  have havg : Fintype.card (Fin (K + 1)) • ((∑ i, w i) / (K + 1)) ≤ ∑ i, w i := by
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact le_of_eq (mul_div_cancel₀ _ hK.ne')
  obtain ⟨j, hj⟩ := Fintype.exists_le_sum_fiber_of_nsmul_le_sum f havg
  let S := Finset.univ.filter (fun i => f i = j)
  have hS : S.Nonempty := by
    by_contra he
    have he' : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change (∑ i, w i) / (K + 1) ≤ ∑ i ∈ S, w i at hj
    rw [he', Finset.sum_empty] at hj
    exact (not_le_of_gt (div_pos hmass hK)) hj
  refine ⟨j, by omega, S, hS, hj, ?_⟩
  intro i hi
  have hfi : f i = j := (Finset.mem_filter.mp hi).2
  simpa only [hfi] using hf i

end WangZahlLot.Obl.wz_multiscale_finite_tower
