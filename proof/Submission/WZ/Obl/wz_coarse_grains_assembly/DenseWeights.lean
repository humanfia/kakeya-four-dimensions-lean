-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.DenseWeights.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- Discarding weights below a prescribed density loses at most half the
total weight when twice the total density cost is affordable. -/
theorem select_dense_weights {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (weight : ι → ENNReal) (cost : ι → ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hcost : ∀ i ∈ S, 0 ≤ cost i)
    (hfinite : ∀ i ∈ S, weight i ≠ ⊤)
    (hmass : O (2 * τ * ∑ i ∈ S, cost i) ≤ ∑ i ∈ S, weight i) :
    ∃ A : Finset ι, A ⊆ S ∧
      (∑ i ∈ S, weight i) ≤ 2 * ∑ i ∈ A, weight i ∧
      ∀ i ∈ A, 0 < weight i ∧ O (τ * cost i) ≤ weight i := by
  classical
  let W (i : ι) : ℝ := (weight i).toReal
  let good (i : ι) : Prop := 0 < W i ∧ τ * cost i ≤ W i
  let A := S.filter good
  have hsum (B : Finset ι) (hBS : B ⊆ S) :
      O (∑ i ∈ B, W i) = ∑ i ∈ B, weight i := by
    calc
      _ = ∑ i ∈ B, O (W i) := ENNReal.ofReal_sum_of_nonneg
        (fun i _ => show 0 ≤ W i from ENNReal.toReal_nonneg)
      _ = _ := Finset.sum_congr rfl (fun i hi => ENNReal.ofReal_toReal (hfinite i (hBS hi)))
  have hmassR : 2 * τ * (∑ i ∈ S, cost i) ≤ ∑ i ∈ S, W i := by
    rw [← hsum S (Finset.Subset.refl _)] at hmass
    exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg))).mp hmass
  have hbad : (∑ i ∈ S.filter (fun i => ¬good i), W i) ≤ τ * ∑ i ∈ S, cost i := by
    calc
      _ ≤ ∑ i ∈ S.filter (fun i => ¬good i), τ * cost i := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hiS, hi⟩ := Finset.mem_filter.mp hi
        by_cases hpos : 0 < W i
        · exact (lt_of_not_ge (fun hd => hi ⟨hpos, hd⟩)).le
        · exact (le_of_not_gt hpos).trans (mul_nonneg hτ (hcost i hiS))
      _ ≤ ∑ i ∈ S, τ * cost i := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun i hi _ => mul_nonneg hτ (hcost i hi))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not S good W
  have hret : (∑ i ∈ S, W i) ≤ 2 * ∑ i ∈ A, W i := by
    dsimp only [A]
    linarith
  refine ⟨A, Finset.filter_subset _ _, ?_, ?_⟩
  · calc
      _ = O (∑ i ∈ S, W i) := (hsum S (Finset.Subset.refl _)).symm
      _ ≤ O (2 * ∑ i ∈ A, W i) := ENNReal.ofReal_le_ofReal hret
      _ = 2 * ∑ i ∈ A, weight i := by
        calc
          _ = O 2 * O (∑ i ∈ A, W i) := ENNReal.ofReal_mul (by norm_num)
          _ = _ := by rw [hsum A (Finset.filter_subset _ _)]; norm_num [O]
  · intro i hi
    obtain ⟨hiS, hpos, hd⟩ := Finset.mem_filter.mp hi
    constructor
    · have hh := ENNReal.ofReal_pos.mpr hpos
      rwa [ENNReal.ofReal_toReal (hfinite i hiS)] at hh
    · exact (ENNReal.ofReal_le_ofReal hd).trans_eq (ENNReal.ofReal_toReal (hfinite i hiS))

end WangZahlLot.Obl.wz_coarse_grains_assembly
