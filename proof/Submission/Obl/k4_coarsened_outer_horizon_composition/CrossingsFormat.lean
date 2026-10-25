import Submission.Obl.k4_coarsened_outer_horizon_composition.Crossings
import Submission.Obl.k4_quadratic_atlas_normalization.RefinementFormat

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open Set MvPolynomial
open Submission.Obl.k4_eligibility_sign_description

private abbrev BF {n : ℕ} (H : ℝ) (D : ℕ) (S : Set (Fin n → ℝ)) : Prop :=
  Submission.Obl.k4_dyadic_crop_worlds.BoolFormat H D S

noncomputable def transverseCoordinate (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2)
    (i : Fin 2) : MvPolynomial (Fin 3) ℝ :=
  ∑ j : Fin 2, C (Q⁻¹ i j) * (X j.succ - C (c j) - X 0 * C (u j))

lemma transverseCoordinate_degree (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2) (i : Fin 2) :
    (transverseCoordinate Q c u i).totalDegree ≤ 1 := by
  apply degree_sum_le
  intro j hj
  apply (degree_C_mul_le _ _).trans
  apply degree_sub_le
  · apply degree_sub_le <;> simp
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp

lemma transverseCoordinate_eval (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : E2)
    (i : Fin 2) (z : Fin 3 → ℝ) :
    eval z (transverseCoordinate Q c u i) =
      (Matrix.toEuclideanLin Q⁻¹ (WithLp.toLp 2 ![z 1, z 2] - c - (z 0) • u)) i := by
  fin_cases i <;>
    simp [transverseCoordinate, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail] <;> ring

private lemma format_nonneg {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) : BF 1 D {z | 0 ≤ eval z P} := by
  refine ⟨1, by norm_num, fun _ => P, fun _ => hP, fun v => v 0, ?_⟩
  intro z
  simp

lemma format_baseCross {κ : ℝ} (hκ : 0 ≤ κ) (t₀ t₁ : ℝ) (c u : E2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    fmt 3 3 2 {z : Fin 3 → ℝ | WithLp.toLp 2 z ∈ baseCross κ t₀ t₁ c u Q} := by
  let P : MvPolynomial (Fin 3) ℝ := C (κ ^ 2) - ∑ i : Fin 2, transverseCoordinate Q c u i ^ 2
  have hP : P.totalDegree ≤ 2 := by
    apply degree_sub_le
    · simp only [MvPolynomial.totalDegree_C]; omega
    · apply degree_sum_le
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans (by
        have := transverseCoordinate_degree Q c u i
        omega)
  have hs := format_nonneg P hP
  have ht₀ := format_nonneg (X (0 : Fin 3) - C t₀)
    (show (X (0 : Fin 3) - C t₀ : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 by
      apply degree_sub_le <;> simp)
  have ht₁ := format_nonneg (C t₁ - X (0 : Fin 3))
    (show (C t₁ - X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 by
      apply degree_sub_le <;> simp)
  have h := (Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.inter ht₀ ht₁).inter hs
  have heq : {z : Fin 3 → ℝ | WithLp.toLp 2 z ∈ baseCross κ t₀ t₁ c u Q} =
      ({z | 0 ≤ eval z (X (0 : Fin 3) - C t₀)} ∩ {z | 0 ≤ eval z (C t₁ - X (0 : Fin 3))}) ∩
        {z | 0 ≤ eval z P} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, map_sub, eval_X, eval_C,
      baseCross, mem_Icc, WithLp.ofLp_toLp, P, eval_sum, eval_pow, transverseCoordinate_eval]
    rw [norm_le_iff _ κ hκ]
    constructor
    · rintro ⟨⟨hl, hu⟩, hn⟩
      exact ⟨⟨by linarith, by linarith⟩, hn⟩
    · rintro ⟨⟨hl, hu⟩, hn⟩
      exact ⟨⟨by linarith, by linarith⟩, hn⟩
  rw [heq]
  exact h.mono (by norm_num) (by decide)

noncomputable def fixedHidden (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) :
    MvPolynomial (Fin 3) ℝ := aeval ![X 0, X 1, X 2, C w] R

lemma fixedHidden_degree (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) :
    (fixedHidden R w).totalDegree ≤ R.totalDegree := by
  apply degree_aeval_le
  intro i
  fin_cases i <;> simp

lemma fixedHidden_eval (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) (z : Fin 3 → ℝ) :
    eval z (fixedHidden R w) = (hiddenPolynomial R (WithLp.toLp 2 z)).eval w := by
  rw [fixedHidden, eval_aeval_real, hiddenPolynomial_eval]
  apply congrArg (fun v : Fin 4 → ℝ => eval v R)
  funext i
  fin_cases i <;> simp

/-- In each fixed hidden bin the crossing predicate is a bounded polynomial
Boolean formula; the curvature alternative needs no quantified hidden variable. -/
theorem format_crossing_bin {κ a : ℝ} (hκ : 0 ≤ κ) (ha : 0 ≤ a)
    (t₀ t₁ b : ℝ) (c u : E2) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) (n : ℤ) :
    fmt 3 9 2 {z : Fin 3 → ℝ | (WithLp.toLp 2 z, n) ∈ crossing κ t₀ t₁ a b c u Q R} := by
  have hd : (MvPolynomial.pderiv 3 R).totalDegree ≤ 2 := (degree_pderiv_le R 3).trans hR
  have hdd : (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R)).totalDegree ≤ 2 :=
    (degree_pderiv_le _ _).trans hd
  have hval := Submission.Obl.k4_quadratic_atlas_normalization.format_abs_le
    (fixedHidden R ((n : ℝ) * a)) ((fixedHidden_degree _ _).trans hR) (3 * κ * a * b)
  have hder := Submission.Obl.k4_quadratic_atlas_normalization.format_abs_ge
    (fixedHidden (MvPolynomial.pderiv 3 R) ((n : ℝ) * a))
    ((fixedHidden_degree _ _).trans hd) (b / (2 * κ))
  have hcur := Submission.Obl.k4_quadratic_atlas_normalization.format_abs_ge
    (C a * fixedHidden (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R)) 0)
    ((degree_C_mul_le _ _).trans ((fixedHidden_degree _ _).trans hdd)) (b / (2 * κ))
  have htest := hval.inter (Submission.Obl.k4_quadratic_atlas_normalization.format_union hder hcur)
  have hbase : BF 3 2 {z : Fin 3 → ℝ | WithLp.toLp 2 z ∈ baseCross κ t₀ t₁ c u Q} :=
    format_baseCross hκ t₀ t₁ c u Q
  have h := hbase.inter htest
  have heq : {z : Fin 3 → ℝ | (WithLp.toLp 2 z, n) ∈ crossing κ t₀ t₁ a b c u Q R} =
      {z : Fin 3 → ℝ | WithLp.toLp 2 z ∈ baseCross κ t₀ t₁ c u Q} ∩
        ({z | |eval z (fixedHidden R ((n : ℝ) * a))| ≤ 3 * κ * a * b} ∩
          ({z | b / (2 * κ) ≤ |eval z (fixedHidden (MvPolynomial.pderiv 3 R) ((n : ℝ) * a))|} ∪
           {z | b / (2 * κ) ≤ |eval z (C a * fixedHidden (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R)) 0)|})) := by
    ext z
    simp only [crossing, binTest, mem_inter_iff, mem_ofPred_eq, Set.mem_union,
      fixedHidden_eval, map_mul, eval_C, hiddenPolynomial_derivative, abs_mul, abs_of_nonneg ha]
    rw [mul_comm a]
  rw [heq]
  exact h.mono (by norm_num) (by decide)

end Submission.Obl.k4_coarsened_outer_horizon_composition
