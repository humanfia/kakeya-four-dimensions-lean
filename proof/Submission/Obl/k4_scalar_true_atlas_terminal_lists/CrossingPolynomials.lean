import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Crossing

/-! Degree-four tests for chart crossings in coefficient/time coordinates. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open Set MeasureTheory MvPolynomial

noncomputable def timePolynomial : MvPolynomial (Fin 6) ℝ := X 5
noncomputable def spatialPolynomial : MvPolynomial (Fin 6) ℝ := X 0 + X 5 * X 1
noncomputable def hiddenPolynomial : MvPolynomial (Fin 6) ℝ := X 2 + X 5 * X 3 + (X 5) ^ 2 * X 4

theorem timePolynomial_degree : timePolynomial.totalDegree ≤ 1 := by simp [timePolynomial]

theorem spatialPolynomial_degree : spatialPolynomial.totalDegree ≤ 2 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by simp)

theorem hiddenPolynomial_degree : hiddenPolynomial.totalDegree ≤ 3 := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_mul _ _).trans
    have hh : ((X (5 : Fin 6) : MvPolynomial (Fin 6) ℝ) ^ 2).totalDegree ≤ 2 :=
      (totalDegree_pow _ _).trans (by simp)
    simpa using Nat.add_le_add_right hh 1

/-- Substituting the affine spatial trajectory into a quadratic predictor
has total degree at most four in coefficients and time. -/
theorem predictor_polynomial (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) :
    ∃ Q : MvPolynomial (Fin 6) ℝ, Q.totalDegree ≤ 4 ∧
      ∀ w, eval w Q = eval ![w 5, w 0 + w 5 * w 1] P := by
  obtain ⟨c, hc⟩ := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.isQuad2_eval P hP
  change ∀ t y, eval ![t, y] P = c 0 + c 1 * t + c 2 * y + c 3 * t ^ 2 +
    c 4 * (t * y) + c 5 * y ^ 2 at hc
  let t := timePolynomial
  let y := spatialPolynomial
  let Q : MvPolynomial (Fin 6) ℝ := C (c 0) + C (c 1) * t + C (c 2) * y +
    C (c 3) * t ^ 2 + C (c 4) * (t * y) + C (c 5) * y ^ 2
  have hadd {F G : MvPolynomial (Fin 6) ℝ} (hF : F.totalDegree ≤ 4)
      (hG : G.totalDegree ≤ 4) : (F + G).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le hF hG)
  have hscale (a : ℝ) (F : MvPolynomial (Fin 6) ℝ) :
      (C a * F).totalDegree ≤ F.totalDegree :=
    (totalDegree_mul _ _).trans (by simp)
  have ht : t.totalDegree ≤ 1 := timePolynomial_degree
  have hy : y.totalDegree ≤ 2 := spatialPolynomial_degree
  have ht2 : (t ^ 2).totalDegree ≤ 2 :=
    (totalDegree_pow _ _).trans (by omega)
  have hty : (t * y).totalDegree ≤ 3 :=
    (totalDegree_mul _ _).trans (by omega)
  have hy2 : (y ^ 2).totalDegree ≤ 4 :=
    (totalDegree_pow _ _).trans (by omega)
  refine ⟨Q, ?_, ?_⟩
  · dsimp only [Q]
    exact hadd (hadd (hadd (hadd (hadd (by simp)
      ((hscale _ _).trans (by omega))) ((hscale _ _).trans (by omega)))
      ((hscale _ _).trans (by omega))) ((hscale _ _).trans (by omega)))
      ((hscale _ _).trans hy2)
  · intro w
    rw [hc]
    simp [Q, t, y, timePolynomial, spatialPolynomial]

/-- At one fixed hidden-bin value, a chart crossing is six polynomial
weak-inequality tests. -/
theorem crossing_polynomial_tests (a Λ s q u v J : ℝ) (c : ℤ)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2) :
    ∃ Q : Fin 6 → MvPolynomial (Fin 6) ℝ,
      (∀ i, (Q i).totalDegree ≤ 4) ∧ ∀ w,
        ((![w 5, w 0 + w 5 * w 1], c) : Observation) ∈ crossing a Λ s q u v J P ↔
          ∀ i, 0 ≤ eval w (Q i) := by
  obtain ⟨F, hF, hFeval⟩ := predictor_polynomial P hP
  let t := timePolynomial
  let y := spatialPolynomial
  let dy : MvPolynomial (Fin 6) ℝ := y - C u - t * C v
  let dx : MvPolynomial (Fin 6) ℝ := C (c : ℝ) - C (a⁻¹) * F
  let Q : Fin 6 → MvPolynomial (Fin 6) ℝ :=
    ![t - C s, C (s + q) - t, C (Λ * J) - dy, C (Λ * J) + dy,
      C (Λ + 1) - dx, C (Λ + 1) + dx]
  have hadd {F G : MvPolynomial (Fin 6) ℝ} (hF : F.totalDegree ≤ 4)
      (hG : G.totalDegree ≤ 4) : (F + G).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le hF hG)
  have hsub {F G : MvPolynomial (Fin 6) ℝ} (hF : F.totalDegree ≤ 4)
      (hG : G.totalDegree ≤ 4) : (F - G).totalDegree ≤ 4 :=
    (totalDegree_sub _ _).trans (max_le hF hG)
  have hconst (c : ℝ) : (C c : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 4 := by simp
  have ht : t.totalDegree ≤ 4 := timePolynomial_degree.trans (by omega)
  have hy : y.totalDegree ≤ 4 := spatialPolynomial_degree.trans (by omega)
  have htv : (t * C v).totalDegree ≤ 4 := (totalDegree_mul _ _).trans (by simpa using ht)
  have hdy : dy.totalDegree ≤ 4 := hsub (hsub hy (hconst _)) htv
  have hdx : dx.totalDegree ≤ 4 := hsub (hconst _)
    ((totalDegree_mul _ _).trans (by simpa using hF))
  refine ⟨Q, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hsub ht (hconst _)
    · exact hsub (hconst _) ht
    · exact hsub (hconst _) hdy
    · exact hadd (hconst _) hdy
    · exact hsub (hconst _) hdx
    · exact hadd (hconst _) hdx
  · intro w
    simp only [Q, Fin.forall_fin_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.forall_fin_zero, and_true, eval_sub, eval_add, eval_C, eval_mul, t, y,
      timePolynomial, spatialPolynomial, eval_X, dx, dy, hFeval]
    change (w 5 ∈ Icc s (s + q) ∧
      |w 0 + w 5 * w 1 - (u + v * w 5)| ≤ Λ * J) ∧
      |(c : ℝ) - eval ![w 5, w 0 + w 5 * w 1] P / a| ≤ Λ + 1 ↔ _
    simp only [mem_Icc, abs_le, div_eq_mul_inv]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨h4, h5⟩⟩
      repeat' constructor
      all_goals nlinarith [h0, h1, h2, h3, h4, h5]
    · rintro ⟨h0, h1, h2, h3, h4, h5⟩
      repeat' constructor
      all_goals nlinarith [h0, h1, h2, h3, h4, h5]

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
