/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ScalarFitTransfer.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Polynomial

noncomputable section

def recoverRowPolynomial (l : ScalarLine) (P : Polynomial ℝ) : RowPolynomial :=
  ![C (l.2 3) + C (2 * l.2 4) * X - C (l.2 1) * P, P]

theorem recoverRowPolynomial_eval_zero (l : ScalarLine) (P : Polynomial ℝ) (t : ℝ) :
    (recoverRowPolynomial l P 0).eval t = l.2 3 + 2 * t * l.2 4 - l.2 1 * P.eval t := by
  simp only [recoverRowPolynomial, Matrix.cons_val_zero, eval_sub, eval_add, eval_C, eval_mul, eval_X]
  ring

theorem recoverRowPolynomial_admissible (l : ScalarLine) (P : Polynomial ℝ)
    {M : ℕ} (hM : 1 ≤ M) {H B : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hcoeff : ∀ e, |l.2 e| ≤ H) (hdeg : P.natDegree ≤ M)
    (hP : ∀ a : ℕ, |P.coeff a| ≤ B) :
    Admissible M (3 * H + (1 + H) * B) (recoverRowPolynomial l P) := by
  have hlin : (C (l.2 3) + C (2 * l.2 4) * X).natDegree ≤ 1 := by compute_degree
  have hdeg0 : (C (l.2 3) + C (2 * l.2 4) * X - C (l.2 1) * P).natDegree ≤ M :=
    (natDegree_sub_le _ _).trans
      (max_le (hlin.trans hM) ((natDegree_C_mul_le _ _).trans hdeg))
  have hcoeff0 (a : ℕ) : |(C (l.2 3) + C (2 * l.2 4) * X - C (l.2 1) * P).coeff a| ≤
      3 * H + (1 + H) * B := by
    have hc : |(C (l.2 3)).coeff a| ≤ H := by
      by_cases ha : a = 0
      · simpa [ha] using hcoeff 3
      · simp only [coeff_C, ite_eq_right ha, abs_zero]
        exact hH
    have hx : |(C (2 * l.2 4) * X).coeff a| ≤ 2 * H := by
      by_cases ha : 1 = a
      · simp only [coeff_C_mul, coeff_X, ite_eq_left ha, mul_one, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left (hcoeff 4) (by norm_num)
      · simp only [coeff_C_mul, coeff_X, ite_eq_right ha, mul_zero, abs_zero]
        positivity
    have hp : |(C (l.2 1) * P).coeff a| ≤ H * B := by
      rw [coeff_C_mul, abs_mul]
      exact mul_le_mul (hcoeff 1) (hP a) (abs_nonneg _) hH
    rw [coeff_sub, coeff_add]
    calc
      _ ≤ |(C (l.2 3)).coeff a + (C (2 * l.2 4) * X).coeff a| +
          |(C (l.2 1) * P).coeff a| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le ((C (l.2 3)).coeff a + (C (2 * l.2 4) * X).coeff a)
            0 ((C (l.2 1) * P).coeff a)
      _ ≤ |(C (l.2 3)).coeff a| + |(C (2 * l.2 4) * X).coeff a| +
          |(C (l.2 1) * P).coeff a| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ H + 2 * H + H * B := add_le_add (add_le_add hc hx) hp
      _ ≤ _ := by nlinarith
  intro e
  fin_cases e
  · exact ⟨hdeg0, hcoeff0⟩
  · refine ⟨hdeg, fun a => (hP a).trans ?_⟩
    nlinarith

theorem scalar_to_row_error (l : ScalarLine) (t : ℝ) (G : Fin 2 → ℝ)
    (F : ℝ) (P : Polynomial ℝ) {H σ δ ε : ℝ} (hH : 0 ≤ H)
    (hv : |l.2 1| ≤ H)
    (hgraph : |l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1| ≤ σ)
    (hrow : |G 1 - F| ≤ δ) (hfit : |F - P.eval t| ≤ ε) :
    ∀ e, |G e - (recoverRowPolynomial l P e).eval t| ≤ σ + (1 + H) * (δ + ε) := by
  have hσ : 0 ≤ σ := (abs_nonneg _).trans hgraph
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hrow
  have hε : 0 ≤ ε := (abs_nonneg _).trans hfit
  have h1 : |G 1 - P.eval t| ≤ δ + ε :=
    (abs_sub_le (G 1) F (P.eval t)).trans (add_le_add hrow hfit)
  have hid : G 0 - (recoverRowPolynomial l P 0).eval t =
      -(l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1) - l.2 1 * (G 1 - P.eval t) := by
    rw [recoverRowPolynomial_eval_zero]
    ring
  have h0 : |G 0 - (recoverRowPolynomial l P 0).eval t| ≤ σ + H * (δ + ε) := by
    rw [hid]
    calc
      _ ≤ |-(l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1)| +
          |l.2 1 * (G 1 - P.eval t)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (-(l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1))
            0 (l.2 1 * (G 1 - P.eval t))
      _ ≤ σ + H * (δ + ε) := by
        rw [abs_neg, abs_mul]
        exact add_le_add hgraph (mul_le_mul hv h1 (abs_nonneg _) hH)
  intro e
  fin_cases e
  · exact h0.trans (by nlinarith)
  · change |G 1 - P.eval t| ≤ _
    exact h1.trans (by nlinarith)

/-- The scalar fit produces both original row polynomials on the SAME
trajectory, SAME block and every original scalar witness time. -/
theorem row_fit_of_scalar_fit
    {E : Set ScalarIncidence} {G : ScalarIncidence → Fin 2 → ℝ}
    (F : ℝ → ℝ) (P : Polynomial ℝ) {p : ScalarIncidence} (hp : p ∈ E)
    {I : Set ℝ} {M : ℕ} (hM : 1 ≤ M) {H B σ δ ε τ : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hcoeff : ∀ e, |p.1.2 e| ≤ H)
    (hdeg : P.natDegree ≤ M) (hP : ∀ a : ℕ, |P.coeff a| ≤ B)
    (hgraph : ∀ z ∈ E, |z.1.2 3 + 2 * z.2 * z.1.2 4 - G z 0 - G z 1 * z.1.2 1| ≤ σ)
    (hrow : ∀ z ∈ E, |G z 1 - F z.2| ≤ δ)
    (hpoint : |F p.2 - P.eval p.2| ≤ ε)
    (hduration : ENNReal.ofReal τ ≤
      volume {t | (p.1, t) ∈ E ∧ t ∈ I ∧ |F t - P.eval t| ≤ ε}) :
    FitsWith E G I M (3 * H + (1 + H) * B) (σ + (1 + H) * (δ + ε)) τ p
      (recoverRowPolynomial p.1 P) := by
  refine ⟨recoverRowPolynomial_admissible p.1 P hM hH hB hcoeff hdeg hP,
    scalar_to_row_error p.1 p.2 (G p) (F p.2) P hH (hcoeff 1)
      (hgraph p hp) (hrow p hp) hpoint, hduration.trans (measure_mono ?_)⟩
  intro t ht
  exact ⟨ht.1, ht.2.1, scalar_to_row_error p.1 t (G (p.1, t)) (F t) P hH (hcoeff 1)
    (hgraph (p.1, t) ht.1) (hrow (p.1, t) ht.1) ht.2.2⟩

end

end Submission.Obl.k4_scalar_graph_residual_discovery
