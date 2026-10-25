/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/Restoration.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialDegree
import Submission.Obl.k4_scalar_grid_parameter_preparation.Remez

/-! Scalar degree restoration from directional tests on positive-mass witness sets. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open MvPolynomial MeasureTheory Set

/-- The polynomial whose evaluation is the third directional test in `(1,v)`. -/
def cubicPolynomial (p : MvPolynomial (Fin 2) ℝ) (v : ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ j : Fin 4, (((3 : ℕ).choose (j : ℕ) : ℝ) * v ^ (j : ℕ)) • thirdPartials p j

theorem eval_cubicPolynomial (p : MvPolynomial (Fin 2) ℝ) (v : ℝ) (x : Fin 2 → ℝ) :
    eval x (cubicPolynomial p v) = cubicTest p x v := by
  simp only [cubicPolynomial, cubicTest, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Algebra.smul_def]
  ring

theorem totalDegree_thirdPartials_le (p : MvPolynomial (Fin 2) ℝ) (j : Fin 4) :
    (thirdPartials p j).totalDegree ≤ p.totalDegree := by
  have hderiv (q : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
      (pderiv i q).totalDegree ≤ q.totalDegree :=
    (Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le q i).trans (Nat.sub_le _ _)
  have hthree (i j k : Fin 2) :
      (pderiv i (pderiv j (pderiv k p))).totalDegree ≤ p.totalDegree :=
    (hderiv _ i).trans ((hderiv _ j).trans (hderiv _ k))
  fin_cases j
  · exact hthree 0 0 0
  · exact hthree 0 0 1
  · exact hthree 0 1 1
  · exact hthree 1 1 1

theorem totalDegree_cubicPolynomial_le (p : MvPolynomial (Fin 2) ℝ) (v : ℝ) :
    (cubicPolynomial p v).totalDegree ≤ p.totalDegree := by
  apply totalDegree_finsetSum_le
  intro j hj
  exact (totalDegree_smul_le _ _).trans (totalDegree_thirdPartials_le p j)

/-- Four directional tests may be known on different positive-outer-measure
sets. Remez transfers them to the box, and restoration preserves every
coefficient budget as well as producing a genuine quadratic. -/
theorem quadratic_restoration_of_witness_sets (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (v : Fin 4 → ℝ) (S : Fin 4 → Set (Fin 2 → ℝ))
      (K η E : ℝ), p.totalDegree ≤ M → 1 ≤ K → 0 < η → η ≤ 1 → 0 ≤ E →
      (∀ i, |v i| ≤ K) → (∀ i j, i ≠ j → K⁻¹ ≤ |v i - v j|) →
      (∀ i, S i ⊆ Set.Icc (0 : Fin 2 → ℝ) 1 ∧ ENNReal.ofReal η ≤ volume (S i) ∧
        ∀ x ∈ S i, |cubicTest p x (v i)| ≤ E) →
      ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 2 ∧
        (∀ b, |q.coeff b| ≤ |p.coeff b|) ∧
        ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
          |eval x p - eval x q| ≤ C * K ^ 18 * (16 * ((M : ℝ) + 1) / η) ^ (2 * M) * E := by
  obtain ⟨C, hC, hrest⟩ := quadraticTruncation_error_bound M
  refine ⟨96 * C, by positivity, ?_⟩
  intro p v S K η E hp hK hη hη1 hE hv hsep htests
  let A : ℝ := (16 * ((M : ℝ) + 1) / η) ^ (2 * M)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hglobal : ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1, ∀ i, |cubicTest p x (v i)| ≤ A * E := by
    intro x hx i
    have h := polynomial_remez_box (cubicPolynomial p (v i)) M
      ((totalDegree_cubicPolynomial_le p _).trans hp) (S i) hη hη1 hE
      (htests i).1 (htests i).2.1
      (by simpa only [eval_cubicPolynomial] using (htests i).2.2) x hx
    simpa only [eval_cubicPolynomial] using h
  have hthird : ∀ x ∈ Set.Icc (0 : Fin 2 → ℝ) 1, ∀ i,
      |eval x (thirdPartials p i)| ≤ 96 * K ^ 18 * (A * E) := by
    intro x hx
    exact thirdPartials_le_of_four_tests p x v hK (mul_nonneg hA hE) hv hsep (hglobal x hx)
  refine ⟨quadraticTruncation M p, totalDegree_quadraticTruncation M p hp,
    quadraticTruncation_coeff_le M p hp, ?_⟩
  intro x hx
  exact (hrest p _ hp (by positivity) hthird x hx).trans_eq (by dsimp [A]; ring)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
