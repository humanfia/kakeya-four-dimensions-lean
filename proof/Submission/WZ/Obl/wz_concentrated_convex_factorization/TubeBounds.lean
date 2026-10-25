-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_concentrated_convex_factorization.TubeBounds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_concentrated_convex_factorization.Coefficient

namespace WangZahlLot.Obl.wz_concentrated_convex_factorization

open Set MeasureTheory Metric
open scoped ENNReal

noncomputable section

lemma tube_ball_lower {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    ENNReal.ofReal (δ ^ 3) ≤ volume (Tube δ x v) := by
  calc
    ENNReal.ofReal (δ ^ 3) ≤ volume (ball x δ) := by
      rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hδ.le,
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.pi_gt_three, pow_pos hδ 3]
    _ ≤ volume (Tube δ x v) := measure_mono
      (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ)

lemma tube_family_upper {ι : Type*} [DecidableEq ι] {δ : ℝ} (hδ : 0 < δ)
    (x v : ι → Space) (S : Finset ι) :
    Upper (fun i => Tube δ (x i) (v i)) (δ ^ 2) S ((S.card : ℝ) / δ) := by
  classical
  intro U hU
  by_cases hc : count (fun i => Tube δ (x i) (v i)) S U = 0
  · simp [hc]
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have hTi : Tube δ (x i) (v i) ⊆ U := (Finset.mem_filter.mp hi).2
  have hvol := (tube_ball_lower hδ (x i) (v i)).trans (measure_mono hTi)
  calc
    ENNReal.ofReal ((count (fun i => Tube δ (x i) (v i)) S U : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal ((S.card : ℝ) * δ ^ 2) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (count_le_card _ _ _)) (sq_nonneg _))
    _ = ENNReal.ofReal ((S.card : ℝ) / δ) * ENNReal.ofReal (δ ^ 3) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal ((S.card : ℝ) / δ) * volume U := mul_le_mul' le_rfl hvol

lemma tube_coefficient_bound {ι : Type*} [DecidableEq ι] {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x v : ι → Space) (S : Finset ι) (hS : S.Nonempty) :
    coefficient (fun i => Tube δ (x i) (v i)) (δ ^ 2) S ≤ (S.card : ℝ) / δ := by
  have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast Finset.card_pos.mpr hS
  apply coefficient_le ((le_div_iff₀ hδ).mpr (by linarith))
  exact tube_family_upper hδ x v S

end
end WangZahlLot.Obl.wz_concentrated_convex_factorization
