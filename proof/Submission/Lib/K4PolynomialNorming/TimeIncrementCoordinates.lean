/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Set MeasureTheory
open scoped BigOperators

namespace Submission.Lib.K4PolynomialNorming

private def prefixSumMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j ≤ i then 1 else 0

private theorem prefixSumMatrix_det (n : ℕ) : (prefixSumMatrix n).det = 1 := by
  have htri : (prefixSumMatrix n).IsLowerTriangular := by
    intro i j hij
    have hji : ¬ j ≤ i := not_le_of_gt (show i < j from hij)
    simp [prefixSumMatrix, hji]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [prefixSumMatrix]

noncomputable def prefixSumLinearEquiv (n : ℕ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ((Matrix.toLin' (prefixSumMatrix n)).equivOfDetNeZero
    (by simp [LinearMap.det_toLin', prefixSumMatrix_det])).toContinuousLinearEquiv

theorem prefixSumLinearEquiv_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    prefixSumLinearEquiv n x i = ∑ j ∈ Finset.Iic i, x j := by
  change (Matrix.toLin' (prefixSumMatrix n) x) i = _
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, dotProduct, prefixSumMatrix, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp

theorem prefixSumLinearEquiv_det (n : ℕ) :
    LinearMap.det (prefixSumLinearEquiv n).toLinearMap = 1 := by
  change LinearMap.det (Matrix.toLin' (prefixSumMatrix n)) = 1
  rw [LinearMap.det_toLin', prefixSumMatrix_det]

theorem prefixSumLinearEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (prefixSumLinearEquiv n) := by
  refine ⟨(prefixSumLinearEquiv n).continuous.measurable, ?_⟩
  change Measure.map (prefixSumLinearEquiv n).toLinearMap volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (by rw [prefixSumLinearEquiv_det]; norm_num), prefixSumLinearEquiv_det]
  simp

/-- Add the starting time to the successive cumulative signed durations. -/
noncomputable def cumulativeTimes (n : ℕ) (start : ℝ) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  (prefixSumLinearEquiv n).toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.addLeft (fun _ : Fin n => start))

theorem cumulativeTimes_apply (n : ℕ) (start : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    cumulativeTimes n start x i = start + ∑ j ∈ Finset.Iic i, x j := by
  change start + prefixSumLinearEquiv n x i = _
  rw [prefixSumLinearEquiv_apply]

theorem cumulativeTimes_measurePreserving (n : ℕ) (start : ℝ) :
    MeasurePreserving (cumulativeTimes n start) :=
  (measurePreserving_add_left volume (fun _ : Fin n => start)).comp
    (prefixSumLinearEquiv_measurePreserving n)

/-- Consecutive time differences, including the fixed starting time. -/
def consecutiveTimeIncrements {n : ℕ} (start : ℝ) (t : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Fin.cons start t : Fin (n + 1) → ℝ) i.succ - (Fin.cons start t : Fin (n + 1) → ℝ) i.castSucc

theorem cumulativeTimes_consecutiveTimeIncrements (n : ℕ) (start : ℝ) (t : Fin n → ℝ) :
    cumulativeTimes n start (consecutiveTimeIncrements start t) = t := by
  ext i
  rw [cumulativeTimes_apply]
  change start + (∑ j ∈ Finset.Iic i,
    ((Fin.cons start t : Fin (n + 1) → ℝ) j.succ -
      (Fin.cons start t : Fin (n + 1) → ℝ) j.castSucc)) = t i
  rw [Fin.sum_Iic_sub]
  simp only [Fin.cons_succ, Fin.cons_zero]
  ring

theorem cumulativeTimes_symm_apply (n : ℕ) (start : ℝ) (t : Fin n → ℝ) :
    (cumulativeTimes n start).symm t = consecutiveTimeIncrements start t := by
  apply (cumulativeTimes n start).injective
  rw [MeasurableEquiv.apply_symm_apply, cumulativeTimes_consecutiveTimeIncrements]

theorem consecutiveTimeIncrements_measurePreserving (n : ℕ) (start : ℝ) :
    MeasurePreserving (consecutiveTimeIncrements (n := n) start) := by
  have h := MeasurePreserving.symm (cumulativeTimes n start)
    (cumulativeTimes_measurePreserving n start)
  have heq : ((cumulativeTimes n start).symm : (Fin n → ℝ) → (Fin n → ℝ)) =
      consecutiveTimeIncrements start := funext (cumulativeTimes_symm_apply n start)
  rw [heq] at h
  exact h

/-- Unit-interval times have signed increments in the coordinate unit box. -/
theorem consecutiveTimeIncrements_mem_unit_box {n : ℕ} {start : ℝ} {t : Fin n → ℝ}
    (hstart : start ∈ Icc 0 1) (ht : ∀ i, t i ∈ Icc 0 1) :
    consecutiveTimeIncrements start t ∈ Icc (-1 : Fin n → ℝ) 1 := by
  have hall : ∀ j : Fin (n + 1), (Fin.cons start t : Fin (n + 1) → ℝ) j ∈ Icc 0 1 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa using hstart
    · intro i
      simpa using ht i
  constructor <;> intro i
  · have ha := hall i.succ
    have hb := hall i.castSucc
    change -1 ≤ (Fin.cons start t : Fin (n + 1) → ℝ) i.succ - (Fin.cons start t : Fin (n + 1) → ℝ) i.castSucc
    linarith [ha.1, ha.2, hb.1, hb.2]
  · have ha := hall i.succ
    have hb := hall i.castSucc
    change (Fin.cons start t : Fin (n + 1) → ℝ) i.succ - (Fin.cons start t : Fin (n + 1) → ℝ) i.castSucc ≤ 1
    linarith [ha.1, ha.2, hb.1, hb.2]

end Submission.Lib.K4PolynomialNorming
