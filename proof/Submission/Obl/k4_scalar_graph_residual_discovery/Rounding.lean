/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file Rounding.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Fits

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory

/-- Uniform evaluation control from coefficient control on the parent time interval. -/
theorem eval_abs_le_of_coeff_le (P : Polynomial ℝ) (M : ℕ) (hP : P.natDegree ≤ M)
    {η : ℝ} (hη : 0 ≤ η) (hc : ∀ a : ℕ, |P.coeff a| ≤ η)
    {t : ℝ} (ht : |t| ≤ 1) : |P.eval t| ≤ ((M : ℝ) + 1) * η := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ a ∈ Finset.range (P.natDegree + 1), |P.coeff a * t ^ a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range (P.natDegree + 1), η := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul, abs_pow]
      exact (mul_le_mul (hc a) (pow_le_one₀ (abs_nonneg t) ht)
        (by positivity) hη).trans_eq (mul_one η)
    _ = ((P.natDegree : ℝ) + 1) * η := by simp
    _ ≤ ((M : ℝ) + 1) * η := by gcongr

/-- Approximate all coefficients by rationals, without increasing the degree. -/
theorem exists_rational_polynomial_approximation (P : Polynomial ℝ) (M : ℕ)
    (hP : P.natDegree ≤ M) {η : ℝ} (hη : 0 < η) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ M ∧
      ∀ a : ℕ, |P.coeff a - ((Q.map (algebraMap ℚ ℝ)).coeff a)| ≤ η := by
  classical
  have hex (a : ℕ) : ∃ q : ℚ, |P.coeff a - (q : ℝ)| < η := by
    obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn
      (show P.coeff a - η < P.coeff a + η by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  choose q hq using hex
  let Q : Polynomial ℚ := ∑ a ∈ Finset.range (M + 1),
    Polynomial.C (q a) * Polynomial.X ^ a
  have hcoeff (a : ℕ) : Q.coeff a = if a < M + 1 then q a else 0 := by
    simp [Q, Polynomial.finsetSum_coeff]
  have hdeg : Q.natDegree ≤ M := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro a ha
    simp [hcoeff, show ¬ a < M + 1 by omega]
  refine ⟨Q, hdeg, fun a => ?_⟩
  rw [Polynomial.coeff_map, hcoeff]
  by_cases ha : a < M + 1
  · simpa [ha] using (hq a).le
  · have hzero := (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP) a (by omega)
    simp [ha, hzero, hη.le]

/-- Rational rounding with independent slack in the coefficient and evaluation budgets. -/
theorem exists_rational_row_approximation (P : RowPolynomial) (M : ℕ)
    (hP : ∀ e, (P e).natDegree ≤ M) {η ξ : ℝ} (hη : 0 < η) (hξ : 0 < ξ) :
    ∃ Q : Fin 2 → Polynomial ℚ, (∀ e, (Q e).natDegree ≤ M) ∧
      (∀ e a, |(P e).coeff a - ((Q e).map (algebraMap ℚ ℝ)).coeff a| ≤ η) ∧
      ∀ (t : ℝ), |t| ≤ 1 → ∀ e,
        |(P e).eval t - ((Q e).map (algebraMap ℚ ℝ)).eval t| ≤ ξ := by
  let ζ := min η (ξ / ((M : ℝ) + 1))
  have hζ : 0 < ζ := lt_min hη (by positivity)
  choose Q hQ hcoeff using fun e =>
    exists_rational_polynomial_approximation (P e) M (hP e) hζ
  refine ⟨Q, hQ, fun e a => (hcoeff e a).trans (min_le_left _ _), ?_⟩
  intro t ht e
  have hdeg : ((P e) - (Q e).map (algebraMap ℚ ℝ)).natDegree ≤ M :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hP e) (Polynomial.natDegree_map_le.trans (hQ e)))
  have hh := eval_abs_le_of_coeff_le
    ((P e) - (Q e).map (algebraMap ℚ ℝ)) M hdeg hζ.le
    (by simpa only [Polynomial.coeff_sub] using hcoeff e) ht
  simp only [Polynomial.eval_sub] at hh
  refine hh.trans ?_
  calc
    ((M : ℝ) + 1) * ζ ≤ ((M : ℝ) + 1) * (ξ / ((M : ℝ) + 1)) := by
      gcongr; exact min_le_right _ _
    _ = ξ := mul_div_cancel₀ _ (by positivity)

/-- A real fit with slack has a rational witness on at least the same original
times. The time interval is never replaced by an interval component. -/
theorem FitsWith.rational_of_slack {α : Type*} {E : Set (α × ℝ)}
    {f : α × ℝ → Fin 2 → ℝ} {I : Set ℝ} {M : ℕ} {C C' δ δ' τ : ℝ}
    {p : α × ℝ} {P : RowPolynomial} (h : FitsWith E f I M C δ τ p P)
    (hI : I ⊆ Icc (-1 : ℝ) 1) (hp : |p.2| ≤ 1) (hC : C < C') (hδ : δ < δ') :
    RationalFits E f I M C' δ' τ p := by
  obtain ⟨Q, hQ, hcoeff, heval⟩ := exists_rational_row_approximation
    P M (fun e => (h.1 e).1) (sub_pos.mpr hC) (sub_pos.mpr hδ)
  have hcoeff' (e : Fin 2) (a : ℕ) :
      |((Q e).map (algebraMap ℚ ℝ)).coeff a| ≤ C' := by
    calc
      _ ≤ |(P e).coeff a - ((Q e).map (algebraMap ℚ ℝ)).coeff a| +
          |(P e).coeff a| := by
        have := abs_sub_le
          (((Q e).map (algebraMap ℚ ℝ)).coeff a) ((P e).coeff a) 0
        simpa only [sub_zero, abs_sub_comm] using this
      _ ≤ (C' - C) + C := add_le_add (hcoeff e a) ((h.1 e).2 a)
      _ = C' := by ring
  have herr (q : α × ℝ) (hq : |q.2| ≤ 1)
      (hfit : ∀ e, |f q e - (P e).eval q.2| ≤ δ) :
      ∀ e, |f q e - ((Q e).map (algebraMap ℚ ℝ)).eval q.2| ≤ δ' := by
    intro e
    calc
      _ ≤ |f q e - (P e).eval q.2| +
          |(P e).eval q.2 - ((Q e).map (algebraMap ℚ ℝ)).eval q.2| :=
        abs_sub_le _ _ _
      _ ≤ δ + (δ' - δ) := add_le_add (hfit e) (heval q.2 hq e)
      _ = δ' := by ring
  refine ⟨Q, ⟨fun e => ⟨Polynomial.natDegree_map_le.trans (hQ e), hcoeff' e⟩,
    herr p hp h.2.1, h.2.2.trans (measure_mono ?_)⟩⟩
  intro t ht
  exact ⟨ht.1, ht.2.1, herr (p.1, t) (abs_le.mpr (hI ht.2.1)) ht.2.2⟩

end Submission.Obl.k4_scalar_graph_residual_discovery
