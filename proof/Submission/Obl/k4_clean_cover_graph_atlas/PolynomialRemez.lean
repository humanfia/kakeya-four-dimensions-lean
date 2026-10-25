-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PolynomialRemez.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PolynomialBounds
import Submission.Obl.k4_clean_cover_graph_atlas.Interface
import Submission.Lib.K4QuadraticSheets.Branch

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial Set Metric MeasureTheory

/-- Mapping coefficients cannot increase total degree. -/
theorem totalDegree_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (P : MvPolynomial σ R) : (P.map φ).totalDegree ≤ P.totalDegree := by
  classical
  apply Finset.sup_le
  intro d hd
  apply le_totalDegree
  apply mem_support_iff.mpr
  intro hz
  apply mem_support_iff.mp hd
  simp [coeff_map, hz]

/-- A polynomial is itself an algebraic sheet, with an equation linear in its value. -/
noncomputable def polynomialGraphRelation {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ :=
  X (Fin.last n) - rename Fin.castSucc P

lemma polynomialGraphRelation_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    polynomialGraphRelation P ≠ 0 := by
  intro hz
  have h₀ : (0 : ℂ) - eval (0 : Fin n → ℂ) P = 0 := by
    simpa [polynomialGraphRelation, MvPolynomial.eval_rename, Function.comp_def] using
      congrArg (eval (Fin.snoc (0 : Fin n → ℂ) 0)) hz
  have h₁ : (1 : ℂ) - eval (0 : Fin n → ℂ) P = 0 := by
    simpa [polynomialGraphRelation, MvPolynomial.eval_rename, Function.comp_def] using
      congrArg (eval (Fin.snoc (0 : Fin n → ℂ) 1)) hz
  have h : (1 : ℂ) = 0 := by linear_combination h₁ - h₀
  exact one_ne_zero h

lemma polynomialGraphRelation_degree {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    (polynomialGraphRelation P).totalDegree ≤ max 1 P.totalDegree := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · rw [totalDegree_X]
    exact le_max_left _ _
  · exact (totalDegree_rename_le _ P).trans (le_max_right _ _)

/-- Complex evaluation agrees with real evaluation on the standard real slice. -/
lemma complex_eval_real {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    eval (fun i : Fin n => (x i : ℂ)) (P.map (algebraMap ℝ ℂ)) =
      ((eval (fun i : Fin n => x i) P : ℝ) : ℂ) := by
  rw [eval_map]
  exact (eval₂_comp (algebraMap ℝ ℂ) (fun i => x i) P).symm

/-- The supplied algebraic Remez comparison includes ordinary multivariable polynomials. -/
theorem exists_real_polynomial_remez (h : algebraicRemez) (n D : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V →
      ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
      ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
        |eval (fun i => x i) P| ≤ C * θ ^ (-C) * V := by
  obtain ⟨C, hC, hremez⟩ := h n (max 1 D)
  refine ⟨C, hC, ?_⟩
  intro P hP E θ V hE hEsub hθ hθ1 hV hmass hbound x hx
  let Q := P.map (algebraMap ℝ ℂ)
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun z => eval (fun i => z i) Q
  have hdeg : (polynomialGraphRelation Q).totalDegree ≤ max 1 D :=
    (polynomialGraphRelation_degree Q).trans
      (max_le_max_left 1 ((totalDegree_map_le _ P).trans hP))
  have hd : DifferentiableOn ℂ F (ball 0 4) :=
    Submission.Lib.K4QuadraticSheets.differentiableOn_eval_comp
      (fun i => (Submission.Lib.K4QuadraticSheets.differentiable_coord i).differentiableOn)
      isOpen_ball Q
  have heq (z : EuclideanSpace ℂ (Fin n)) :
      eval (Fin.snoc (fun i : Fin n => z i) (F z)) (polynomialGraphRelation Q) = 0 := by
    simp [polynomialGraphRelation, F, MvPolynomial.eval_rename, Function.comp_def]
  have hreal (y : EuclideanSpace ℝ (Fin n)) :
      (F (WithLp.toLp 2 (fun i => (y i : ℂ)))).im = 0 := by
    change (eval (fun i : Fin n => (y i : ℂ)) (P.map (algebraMap ℝ ℂ))).im = 0
    rw [complex_eval_real]
    rfl
  have hb (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ E) :
      ‖F (WithLp.toLp 2 (fun i => (y i : ℂ)))‖ ≤ V := by
    change ‖eval (fun i : Fin n => (y i : ℂ)) (P.map (algebraMap ℝ ℂ))‖ ≤ V
    rw [complex_eval_real, Complex.norm_real, Real.norm_eq_abs]
    exact hbound y hy
  have hh := hremez (polynomialGraphRelation Q) F (polynomialGraphRelation_ne_zero Q) hdeg hd
    (fun z _ => heq z) (fun y _ => hreal y) E θ V hE hEsub hθ hθ1 hV hmass hb x hx
  change ‖eval (fun i : Fin n => (x i : ℂ)) (P.map (algebraMap ℝ ℂ))‖ ≤ _ at hh
  simpa only [complex_eval_real, Complex.norm_real, Real.norm_eq_abs] using hh

/-- A positive-volume matched projection controls the coefficients used in stable-sheet
preparation, with constants depending only on dimension and degree. -/
theorem exists_polynomial_remez_coefficient_bound (h : algebraicRemez) (n D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧ ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V →
      ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
      ∀ d, |P.coeff d| ≤ K * (C * θ ^ (-C) * V) := by
  obtain ⟨K, hK, hcoeff⟩ := exists_polynomial_coefficient_bound n D
  obtain ⟨C, hC, hremez⟩ := exists_real_polynomial_remez h n D
  refine ⟨K, C, hK, hC, ?_⟩
  intro P hP E θ V hE hEsub hθ hθ1 hV hmass hbound d
  apply hcoeff P hP (C * θ ^ (-C) * V) (by positivity)
  exact hremez P hP E θ V hE hEsub hθ hθ1 hV hmass hbound

end Submission.Obl.k4_clean_cover_graph_atlas
