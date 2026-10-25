import Submission.Lib.K4ModelReduction.RawCoefficients

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Explicit quadratic Boolean format of the smoothed coefficient components. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set MvPolynomial
open scoped ENNReal

noncomputable def coefficientBallPolynomial (a : EuclideanSpace ℝ (Fin 3))
    (I : Fin 3 → Fin 6) (r : ℝ) : MvPolynomial (Fin 6) ℝ :=
  (∑ j, (X (I j) - C (a j)) ^ 2) - C (r ^ 2)

theorem coefficientBallPolynomial_degree (a : EuclideanSpace ℝ (Fin 3))
    (I : Fin 3 → Fin 6) (r : ℝ) : (coefficientBallPolynomial a I r).totalDegree ≤ 2 := by
  apply (totalDegree_sub_C_le _ _).trans
  apply totalDegree_finsetSum_le
  intro j _
  refine (totalDegree_pow _ 2).trans ?_
  have h : (X (I j) - C (a j) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := by
    exact (totalDegree_sub_C_le _ _).trans_eq (totalDegree_X _)
  omega

theorem coefficientBallPolynomial_eval (a : EuclideanSpace ℝ (Fin 3))
    (I : Fin 3 → Fin 6) (r : ℝ) (x : Fin 6 → ℝ) :
    eval x (coefficientBallPolynomial a I r) =
      ‖(WithLp.toLp 2 (fun j => x (I j)) : EuclideanSpace ℝ (Fin 3)) - a‖ ^ 2 - r ^ 2 := by
  simp only [coefficientBallPolynomial, map_sub, map_sum, map_pow, eval_X, eval_C,
    EuclideanSpace.real_norm_sq_eq]
  rfl

theorem coefficientBallPolynomial_neg_iff (a : EuclideanSpace ℝ (Fin 3))
    (I : Fin 3 → Fin 6) {r : ℝ} (hr : 0 < r) (x : Fin 6 → ℝ) :
    eval x (coefficientBallPolynomial a I r) < 0 ↔
      (WithLp.toLp 2 (fun j => x (I j)) : EuclideanSpace ℝ (Fin 3)) ∈ ball a r := by
  rw [coefficientBallPolynomial_eval, mem_ball, dist_eq_norm]
  have hn := norm_nonneg ((WithLp.toLp 2 (fun j => x (I j)) : EuclideanSpace ℝ (Fin 3)) - a)
  constructor <;> intro h <;> nlinarith

/-- Each smoothed component uses exactly two quadratic tests in six
coordinates, including the correct strict ball boundaries. -/
theorem rawCoefficientRegion_format (b s : EuclideanSpace ℝ (Fin 3))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : Fin 2 → MvPolynomial (Fin 6) ℝ,
      (∀ i, (p i).totalDegree ≤ 2) ∧
      ∃ B : (Fin 2 → Bool) → Bool,
        ∀ x, x ∈ coefficientPairEquiv ⁻¹' (ball b (δ / 4) ×ˢ ball s (δ / 4)) ↔
          B (fun i => decide (0 ≤ eval x (p i))) = true := by
  classical
  let pb := coefficientBallPolynomial b (fun j => j.castAdd 3) (δ / 4)
  let ps := coefficientBallPolynomial s (fun j => j.natAdd 3) (δ / 4)
  refine ⟨![pb, ps], ?_, (fun v => !v 0 && !v 1), ?_⟩
  · intro i
    fin_cases i <;> exact coefficientBallPolynomial_degree _ _ _
  · intro x
    have hb : eval x pb < 0 ↔ (coefficientPairEquiv x).1 ∈ ball b (δ / 4) :=
      coefficientBallPolynomial_neg_iff b _ (by positivity) x
    have hs : eval x ps < 0 ↔ (coefficientPairEquiv x).2 ∈ ball s (δ / 4) :=
      coefficientBallPolynomial_neg_iff s _ (by positivity) x
    have hbool (a : ℝ) : (!decide (0 ≤ a)) = true ↔ a < 0 := by
      by_cases ha : 0 ≤ a
      · simp [ha, not_lt_of_ge ha]
      · simp [ha, lt_of_not_ge ha]
    change ((coefficientPairEquiv x).1 ∈ ball b (δ / 4) ∧
      (coefficientPairEquiv x).2 ∈ ball s (δ / 4)) ↔
        (!decide (0 ≤ eval x pb) && !decide (0 ≤ eval x ps)) = true
    rw [Bool.and_eq_true, hbool, hbool]
    exact and_congr hb.symm hs.symm

theorem norm_le_of_mem_coefficientBall {b x : EuclideanSpace ℝ (Fin 3)} {δ R : ℝ}
    (hb : ‖b‖ ≤ R) (hx : x ∈ ball b (δ / 4)) : ‖x‖ ≤ R + δ / 4 := by
  have hdist : ‖x - b‖ ≤ δ / 4 := by
    exact (by simpa only [mem_ball, dist_eq_norm] using hx : ‖x - b‖ < δ / 4).le
  calc
    ‖x‖ = ‖(x - b) + b‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - b‖ + ‖b‖ := norm_add_le _ _
    _ ≤ δ / 4 + R := add_le_add hdist hb
    _ = _ := add_comm _ _

theorem rawCoefficientRegion_bound (b s : EuclideanSpace ℝ (Fin 3))
    {δ R : ℝ} (hb : ‖b‖ ≤ R) (hs : ‖s‖ ≤ R)
    {x : Fin 6 → ℝ} (hx : x ∈ coefficientPairEquiv ⁻¹'
      (ball b (δ / 4) ×ˢ ball s (δ / 4))) : ∀ i, |x i| ≤ R + δ / 4 := by
  intro i
  have hb' := norm_le_of_mem_coefficientBall hb hx.1
  have hs' := norm_le_of_mem_coefficientBall hs hx.2
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
  · rw [← coefficientPairEquiv_intercept x j, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ _).trans hb'
  · rw [← coefficientPairEquiv_slope x j, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ _).trans hs'

end Submission.Lib.K4ModelReduction
