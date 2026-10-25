import Mathlib

/-
Adapted from this LOT tree, obligation o003, session x0004, commit cf36787,
Submission/Obl/k4_multilinear_kakeya/{Plane,Scaling,Density}.lean.
Only the tube definitions and their monotonicity properties are needed here.
-/

namespace Submission.Obl.k4_mk_grid_transfer

open MeasureTheory Set
open scoped ENNReal

def lineTube {n : ℕ} (r : ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.thickening r (Set.range fun t : ℝ => a + t • e)

lemma measurableSet_lineTube {n : ℕ} (r : ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (lineTube r a e) :=
  Metric.isOpen_thickening.measurableSet

noncomputable def tubeSum {n : ℕ} {N : Fin n → ℕ} (r : ℝ)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ T : ((i : Fin n) → Fin (N i)),
    |(Matrix.of fun i j : Fin n => e i (T i) j).det| *
      ∏ i, (w i (T i) * (lineTube r (a i (T i)) (e i (T i))).indicator
        (fun _ => (1 : ℝ)) x)

lemma tubeSum_nonneg {n : ℕ} {N : Fin n → ℕ} (r : ℝ)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (hw : ∀ i k, 0 ≤ w i k)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ tubeSum r a e w x := by
  unfold tubeSum
  exact Finset.sum_nonneg fun T _ => mul_nonneg (abs_nonneg _)
    (Finset.prod_nonneg fun i _ => mul_nonneg (hw i (T i))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _))

lemma measurable_tubeSum {n : ℕ} {N : Fin n → ℕ} (r : ℝ)
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) : Measurable (tubeSum r a e w) := by
  unfold tubeSum
  apply Finset.measurable_sum
  intro T _
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.mul (measurable_const.indicator (measurableSet_lineTube _ _ _))

lemma tubeSum_le_of_indicator_le {n : ℕ} {N : Fin n → ℕ} {r s : ℝ}
    (a b e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (hw : ∀ i k, 0 ≤ w i k)
    (x y : EuclideanSpace ℝ (Fin n))
    (h : ∀ i k, (lineTube r (a i k) (e i k)).indicator (fun _ => (1 : ℝ)) x ≤
      (lineTube s (b i k) (e i k)).indicator (fun _ => (1 : ℝ)) y) :
    tubeSum r a e w x ≤ tubeSum s b e w y := by
  unfold tubeSum
  apply Finset.sum_le_sum
  intro T _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg (hw i (T i)) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · intro i _
    exact mul_le_mul_of_nonneg_left (h i (T i)) (hw i (T i))

lemma lineTube_mono_center {n : ℕ} {x y a e : EuclideanSpace ℝ (Fin n)}
    (hxy : dist x y < 2) (hx : x ∈ lineTube 1 a e) : y ∈ lineTube 3 a e := by
  obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.mp hx
  apply Metric.mem_thickening_iff.mpr
  refine ⟨z, hz, ?_⟩
  have htri := dist_triangle y x z
  rw [dist_comm y x] at htri
  linarith

lemma tubeSum_le_nearby {n : ℕ} {N : Fin n → ℕ}
    (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ) (hw : ∀ i k, 0 ≤ w i k)
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : dist x y < 2) :
    tubeSum 1 a e w x ≤ tubeSum 3 a e w y := by
  apply tubeSum_le_of_indicator_le a a e w hw x y
  intro i k
  by_cases hx : x ∈ lineTube 1 (a i k) (e i k)
  · have hy := lineTube_mono_center hxy hx
    simp [hx, hy]
  · simp [hx, Set.indicator_nonneg (fun _ _ => zero_le_one)]

end Submission.Obl.k4_mk_grid_transfer
