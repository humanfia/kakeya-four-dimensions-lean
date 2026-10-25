import Submission.Obl.k4_scalar_tangent_isotropic_improvement.LinePolynomials

/-! Whole-block potential fits give cubic tests in normalized base coordinates. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

theorem exists_normalized_trajectory_cubicTest_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (a : Fin 5 → ℝ) (t₀ y₀ h E : ℝ),
      p.totalDegree ≤ D → 0 < h → 0 ≤ E →
      (∀ t ∈ Set.Icc t₀ (t₀ + h),
        |a 2 + t * a 3 + t ^ 2 * a 4 -
          MvPolynomial.eval ![(t - t₀) / h, (a 0 + t * a 1 - y₀) / h] p| ≤ E) →
      ∀ t ∈ Set.Icc t₀ (t₀ + h),
        |cubicTest p ![(t - t₀) / h, (a 0 + t * a 1 - y₀) / h] (a 1)| ≤ C * E := by
  obtain ⟨C, hC, hline⟩ := exists_cubicTest_bound_of_line_fit D
  refine ⟨C, hC, ?_⟩
  intro p a t₀ y₀ h E hp hh hE hfit
  let f : Polynomial ℝ := Polynomial.C (a 2 + t₀ * a 3 + t₀ ^ 2 * a 4) +
    Polynomial.C (h * a 3 + 2 * t₀ * h * a 4) * Polynomial.X +
    Polynomial.C (h ^ 2 * a 4) * Polynomial.X ^ 2
  have hf : f.natDegree ≤ 2 := by dsimp [f]; compute_degree!
  have hfeval (s : ℝ) : f.eval s = a 2 + (t₀ + h * s) * a 3 + (t₀ + h * s) ^ 2 * a 4 := by
    simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  have hbase (s : ℝ) :
      ![s, (a 0 + t₀ * a 1 - y₀) / h + a 1 * s] =
      ![((t₀ + h * s) - t₀) / h, (a 0 + (t₀ + h * s) * a 1 - y₀) / h] := by
    ext i
    fin_cases i <;> simp <;> field_simp [hh.ne'] <;> ring
  have hnormalized : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |f.eval s - MvPolynomial.eval
        ![0 + s, (a 0 + t₀ * a 1 - y₀) / h + a 1 * s] p| ≤ E := by
    intro s hs
    have htime : t₀ + h * s ∈ Set.Icc t₀ (t₀ + h) := by
      constructor
      · nlinarith [mul_nonneg hh.le hs.1]
      · nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hs.2)]
    simpa only [zero_add, hfeval, hbase] using hfit (t₀ + h * s) htime
  have htests := hline p ![0, (a 0 + t₀ * a 1 - y₀) / h] (a 1) f E hp hf hE hnormalized
  intro t ht
  let s := (t - t₀) / h
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hh.le, (div_le_one hh).mpr (by linarith [ht.2])⟩
  have htime : t₀ + h * s = t := by dsimp [s]; field_simp [hh.ne']; ring
  have htest := htests s hs
  change |cubicTest p ![0 + s, (a 0 + t₀ * a 1 - y₀) / h + a 1 * s] (a 1)| ≤ C * E at htest
  rw [zero_add, hbase, htime] at htest
  exact htest

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
