import Mathlib
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace Submission.Lib.KakeyaCovering

/-- A finite net bounds outer three-dimensional volume; no measurability is needed. -/
theorem slope_volume_le_card_of_cover {A : Set (EuclideanSpace ℝ (Fin 3))}
    (F : Finset (EuclideanSpace ℝ (Fin 3))) {r : ℝ} (hr : 0 ≤ r)
    (hcover : A ⊆ ⋃ x ∈ F, closedBall x r) :
    volume A ≤ ENNReal.ofReal ((F.card : ℝ) * 16 * r ^ 3) := by
  have hb (x : EuclideanSpace ℝ (Fin 3)) :
      volume (closedBall x r) ≤ ENNReal.ofReal (16 * r ^ 3) := by
    rw [EuclideanSpace.volume_closedBall_fin_three, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hπ : Real.pi * 4 / 3 ≤ 16 := by linarith [Real.pi_lt_four]
    nlinarith [mul_le_mul_of_nonneg_left hπ (pow_nonneg hr 3)]
  calc
    volume A ≤ ∑ x ∈ F, volume (closedBall x r) :=
      (measure_mono hcover).trans (measure_biUnion_finset_le F _)
    _ ≤ ∑ x ∈ F, ENNReal.ofReal (16 * r ^ 3) := Finset.sum_le_sum fun x _ => hb x
    _ = ENNReal.ofReal ((F.card : ℝ) * 16 * r ^ 3) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp [mul_assoc]

/-- A bounded set of positive outer measure supplies many separated slopes. -/
theorem exists_many_separated_slopes {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : Bornology.IsBounded A) {r a : ℝ} (hr : 0 < r)
    (ha : ENNReal.ofReal a ≤ volume A) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin 3)), (↑F : Set _) ⊆ A ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) ∧
      a ≤ (F.card : ℝ) * 16 * r ^ 3 := by
  obtain ⟨F, hFA, hsep, hcover⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover
      (hA.isCompact_closure.totallyBounded.subset subset_closure) hr
  refine ⟨F, hFA, hsep, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    (ha.trans (slope_volume_le_card_of_cover F hr.le hcover))

end Submission.Lib.KakeyaCovering
