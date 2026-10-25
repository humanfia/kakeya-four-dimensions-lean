import Submission.Obl.k4_adapted_oscillation_tests
import Submission.Obl.k4_smooth_polynomial_ham_sandwich
import Submission.Obl.k4_prescribed_polynomial_visibility.PolynomialSmooth
import Submission.Obl.k4_prescribed_polynomial_visibility.VolumeShrink

namespace Submission.Obl.k4_prescribed_polynomial_visibility

open MeasureTheory
open scoped ENNReal

/-- The regularizer bounds every old unit body, including those with zero demand. -/
theorem unitBody_volume_lt_top {n : ℕ}
    (V : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hV : ∀ v, ‖v‖ ≤ V v) : volume (unitBody V) < ⊤ := by
  have hsub : unitBody V ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro v hv
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hV v).trans hv
  exact lt_of_le_of_lt (measure_mono hsub) Metric.isBounded_closedBall.measure_lt_top

/-- Aggregating the two independent test lemmas yields a common improving polynomial.
Only cells whose old bodies exceed their target contribute tests. -/
theorem exists_polynomial_improvement (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin n)) (M : Fin m → ℝ),
        (∀ q, 0 ≤ M q) → (∑ q, M q) = 1 →
        ∀ T : ℝ, 1 ≤ T →
        ∀ V : Fin m → Seminorm ℝ (EuclideanSpace ℝ (Fin n)),
          (∀ q v, ‖v‖ ≤ V q v) →
          ∃ p : MvPolynomial (Fin n) ℝ, (p.totalDegree : ℝ) ≤ C * T ∧
            ∀ q, 0 < M q →
              ENNReal.ofReal ((T ^ n * M q)⁻¹) < volume (unitBody (V q)) →
              ∃ v, V q v ≤ 1 ∧ 3 * (8 : ℝ) ^ n ≤ polynomialVariation p (c q) v := by
  classical
  obtain ⟨C, hC, htests⟩ := Submission.k4_adapted_oscillation_tests n hn
    (3 * (8 : ℝ) ^ n) (by positivity)
  refine ⟨(n : ℝ) * (C + 1), mul_pos (by exact_mod_cast hn) (by linarith), ?_⟩
  intro m c M hM hsum T hT V hV
  let active : Fin m → Prop := fun q =>
    0 < M q ∧ ENNReal.ofReal ((T ^ n * M q)⁻¹) < volume (unitBody (V q))
  let Active := {q : Fin m // active q}
  choose k Q hk hQ hcert using fun q : Active =>
    htests (V q.val) (continuous_seminorm _) (hV q.val) (c q.val)
  let I := (q : Active) × Fin (k q)
  have hmass : (∑ q : Active, M q.val) ≤ 1 := by
    let s := Finset.univ.filter active
    calc
      (∑ q : Active, M q.val) = ∑ q ∈ s, M q := by
        exact (Finset.sum_subtype s (by intro q; simp [s]) M).symm
      _ ≤ ∑ q : Fin m, M q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun q _ _ => hM q)
      _ = 1 := hsum
  have hcount_cell : ∀ q : Active, (k q : ℝ) ≤ C * (T ^ n * M q.val) := by
    intro q
    have hpos : 0 < T ^ n * M q.val :=
      mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hT) _) q.property.1
    have hfinite := unitBody_volume_lt_top (V q.val) (hV q.val)
    have hreal : (T ^ n * M q.val)⁻¹ < (volume (unitBody (V q.val))).toReal := by
      have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite.ne).mpr
        q.property.2
      simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le)] using h
    exact (hk q).trans
      (mul_le_mul_of_nonneg_left (inv_le_of_inv_le₀ hpos hreal.le) hC.le)
  have hcount : (Fintype.card I : ℝ) ≤ C * T ^ n := by
    calc
      (Fintype.card I : ℝ) = ∑ q : Active, (k q : ℝ) := by
        simp only [I, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
      _ ≤ ∑ q : Active, C * (T ^ n * M q.val) :=
        Finset.sum_le_sum (fun q _ => hcount_cell q)
      _ = C * T ^ n * ∑ q : Active, M q.val := by
        simp_rw [← mul_assoc]
        rw [Finset.mul_sum]
      _ ≤ C * T ^ n * 1 :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = C * T ^ n := mul_one _
  have hscale : 1 ≤ (C + 1) * T := by nlinarith
  have hbudget : (Fintype.card I : ℝ) ≤ ((C + 1) * T) ^ n := by
    refine hcount.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((le_add_of_nonneg_right zero_le_one).trans
        (le_self_pow₀ (by linarith : 1 ≤ C + 1) (by omega))) (by positivity)
  let e := Fintype.equivFin I
  let Qall : Fin (Fintype.card I) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => Q (e.symm i).1 (e.symm i).2
  obtain ⟨p, hpdeg, hposc⟩ := Submission.k4_smooth_polynomial_ham_sandwich n hn
    ((C + 1) * T) hscale (Fintype.card I) Qall hbudget
    (fun i => ⟨(hQ (e.symm i).1 (e.symm i).2).1,
      (hQ (e.symm i).1 (e.symm i).2).2.1⟩)
  refine ⟨p, by simpa only [mul_assoc] using hpdeg, ?_⟩
  intro q hMq hactive
  let qa : Active := ⟨q, hMq, hactive⟩
  apply hcert qa (arctanPolynomial p) (contDiff_arctanPolynomial p 1)
  intro h
  have hi : e.symm (e ⟨qa, h⟩) = ⟨qa, h⟩ := e.symm_apply_apply _
  have he : Qall (e ⟨qa, h⟩) = Q qa h := congrArg (fun i : I => Q i.1 i.2) hi
  have hh := hposc (e ⟨qa, h⟩)
  rw [he] at hh
  exact hh

end Submission.Obl.k4_prescribed_polynomial_visibility
