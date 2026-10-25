/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.PolynomialRemez

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- A polynomial bounded on the unit circle has every coefficient bounded
by the same constant. This is an immediate consequence of Mathlib's Parseval
identity, and avoids a separate interpolation system. -/
theorem complex_polynomial_coeff_norm_le_of_unit_circle (p : Polynomial ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) (n : ℕ) :
    ‖p.coeff n‖ ≤ M := by
  classical
  by_cases hn : p.coeff n = 0
  · simpa [hn] using hM
  have hmem : n ∈ p.support := Polynomial.mem_support_iff.mpr hn
  have hsingle : ‖p.coeff n‖ ^ 2 ≤ ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖p.coeff i‖ ^ 2) (fun i hi => sq_nonneg _) hmem
  rw [p.sum_sq_norm_coeff_eq_circleAverage] at hsingle
  have hcont : Continuous (fun z : ℂ => ‖p.eval z‖ ^ 2) := by fun_prop
  have havg : Real.circleAverage (fun z => ‖p.eval z‖ ^ 2) 0 1 ≤ M ^ 2 := by
    apply Real.circleAverage_mono_on_of_le_circle hcont.continuousOn.circleIntegrable'
    intro z hz
    have hz' : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound z hz') 2
  have hsq := hsingle.trans havg
  nlinarith [norm_nonneg (p.coeff n)]

/-- Positive-measure real observations control every complex coefficient,
with an explicit fixed power of the reciprocal observation measure. -/
theorem complex_polynomial_coeff_le_of_small_values (p : Polynomial ℂ) (D : ℕ)
    (hD : p.natDegree ≤ D) (E : Set ℝ) (ℓ A ε : ℝ) (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal ℓ ≤ volume E) (hE : ∀ t ∈ E, |t| ≤ A)
    (hsmall : ∀ t ∈ E, ‖p.eval (t : ℂ)‖ ≤ ε) (n : ℕ) :
    ‖p.coeff n‖ ≤ (1 + 4 * (D + 1 : ℕ) * (1 + A) / ℓ) ^ D * ε := by
  apply complex_polynomial_coeff_norm_le_of_unit_circle p _ (by positivity) _ n
  intro z hz
  apply polynomial_remez_of_bounded_distance p D hD E ℓ (1 + A) ε hℓ (by positivity) hmass hsmall z
  intro t ht
  calc
    ‖z - (t : ℂ)‖ ≤ ‖z‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
    _ = 1 + |t| := by rw [hz, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 + A := add_le_add le_rfl (hE t ht)

/-- Real coefficients inherit the same explicit Remez bound. -/
theorem real_polynomial_coeff_le_of_small_values (p : Polynomial ℝ) (D : ℕ)
    (hD : p.natDegree ≤ D) (E : Set ℝ) (ℓ A ε : ℝ) (hℓ : 0 < ℓ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal ℓ ≤ volume E) (hE : ∀ t ∈ E, |t| ≤ A)
    (hsmall : ∀ t ∈ E, |p.eval t| ≤ ε) (n : ℕ) :
    |p.coeff n| ≤ (1 + 4 * (D + 1 : ℕ) * (1 + A) / ℓ) ^ D * ε := by
  have heval (t : ℝ) : ‖(p.map (algebraMap ℝ ℂ)).eval (t : ℂ)‖ = |p.eval t| := by
    rw [Polynomial.eval_map]
    change ‖p.eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) t)‖ = _
    rw [Polynomial.eval₂_at_apply]
    exact Complex.norm_real _
  have h := complex_polynomial_coeff_le_of_small_values (p.map (algebraMap ℝ ℂ)) D
    (by simpa using hD) E ℓ A ε hℓ hA hε hmass hE (fun t ht => by rw [heval]; exact hsmall t ht) n
  simpa using h

end Submission.Lib.K4PolynomialNorming
