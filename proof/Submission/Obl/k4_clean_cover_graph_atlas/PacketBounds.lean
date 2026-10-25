import Submission.Obl.k4_clean_cover_graph_atlas.GroupCoords

namespace Submission.Obl.k4_clean_cover_graph_atlas
open MeasureTheory MvPolynomial Set Submission.Lib.K4XInterface

/-- Affine packet normalization never increases the degree of a test. -/
theorem normPoly_totalDegree_le (T j : ℕ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (normPoly T j c u Q B P).totalDegree ≤ P.totalDegree := by
  have hadd {P Q : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1) :
      (P + Q).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le hP hQ)
  have hterm (a : ℝ) (i : Fin 4) : (MvPolynomial.C a * MvPolynomial.X i).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  have hconst (a : ℝ) : (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := by simp
  have hsubst (e : Fin 4) : (packetSubst T j c u Q B e).totalDegree ≤ 1 := by
    fin_cases e <;> simp only [packetSubst, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    all_goals solve_by_elim (maxDepth := 8) [hadd, hterm, hconst]
  simpa only [normPoly, one_mul] using totalDegree_eval₂C_le (packetSubst T j c u Q B) hsubst P

/-- The original old packet fits in a normalized base ball of radius κ+1.
This bound holds before any choice of a small comparison box. -/
theorem normBase_bound_of_chart {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T j : ℕ} {r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (hc : gchart Nk M D κ T (j : ℝ) r Bv Ev c u Q R A F ex)
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A) {t : ℝ}
    (ht : t ∈ Icc ((j : ℝ) / 2 ^ T) (((j : ℝ) + 1) / 2 ^ T)) :
    ‖normBase T j c u Q l t‖ ≤ κ + 1 := by
  have hz : ‖zc Q c u l t‖ ≤ κ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hA, _⟩ := hc
    exact ((hA l hl).2.2 t ht).1
  have hκ : 0 ≤ κ := (norm_nonneg _).trans hz
  have hp : 0 < (2 : ℝ) ^ T := by positivity
  have ht0 : 0 ≤ (2 : ℝ) ^ T * t - j := by
    have h := (div_le_iff₀ hp).mp ht.1
    nlinarith
  have ht1 : (2 : ℝ) ^ T * t - j ≤ 1 := by
    have h := (le_div_iff₀ hp).mp ht.2
    nlinarith
  have htsq : ((2 : ℝ) ^ T * t - j) ^ 2 ≤ 1 := by nlinarith
  have hzs := pow_le_pow_left₀ (norm_nonneg _) hz 2
  rw [norm_sq_fin2] at hzs
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by linarith : 0 ≤ κ + 1), Fin.sum_univ_three]
  simp only [normBase, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  nlinarith

end Submission.Obl.k4_clean_cover_graph_atlas
