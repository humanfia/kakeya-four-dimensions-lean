-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_estimate_equivalence.Slab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_estimate_equivalence

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya

/-- Every tube contains a ball with volume at least `δ³`. -/
theorem cube_le_tube_volume {δ : ℝ} (hδ : 0 < δ) (x v : Space) :
    ENNReal.ofReal (δ ^ 3) ≤ volume (thickening δ (segment ℝ x (x + v))) := by
  apply le_trans _ (measure_mono (ball_subset_thickening (left_mem_segment ℝ x (x + v)) δ))
  rw [EuclideanSpace.volume_ball_fin_three]
  calc
    ENNReal.ofReal (δ ^ 3) ≤ ENNReal.ofReal (δ ^ 3 * (Real.pi * 4 / 3)) := by
      apply ENNReal.ofReal_le_ofReal
      have hpi := Real.pi_gt_three
      nlinarith [pow_pos hδ 3]
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ.le]

/-- A universal volume-normalized counting bound, with no geometric conditions on `W`. -/
theorem universal_volume_count {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (W : Set Space) :
    ENNReal.ofReal ({i : Fin n | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W}.ncard : ℝ) ≤
      ENNReal.ofReal (δ ^ (-3 : ℝ) * (n : ℝ)) * volume W := by
  let I := {i : Fin n | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W}
  change ENNReal.ofReal (I.ncard : ℝ) ≤ _
  rcases I.eq_empty_or_nonempty with hI | ⟨i, hi⟩
  · simp [hI]
  have hcount : I.ncard ≤ n := by simpa using I.ncard_le_card
  have hvol : ENNReal.ofReal (δ ^ 3) ≤ volume W :=
    (cube_le_tube_volume hδ (x i) (v i)).trans (measure_mono hi)
  calc
    ENNReal.ofReal (I.ncard : ℝ) ≤ ENNReal.ofReal (n : ℝ) :=
      ENNReal.ofReal_le_ofReal (by exact_mod_cast hcount)
    _ = ENNReal.ofReal (δ ^ (-3 : ℝ) * (n : ℝ)) * ENNReal.ofReal (δ ^ 3) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_neg hδ.le, Real.rpow_ofNat]
      field_simp
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_estimate_equivalence
