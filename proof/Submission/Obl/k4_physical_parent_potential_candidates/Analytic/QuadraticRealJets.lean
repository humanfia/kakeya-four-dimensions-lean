-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/QuadraticRealJets.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/QuadraticRealJets.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/QuadraticRealJets.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RationalRealJets
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RationalQuadratic
import Submission.Obl.k4_eligibility_sign_description.Signs
import Submission.Obl.k4_quadratic_sheet_continuation.Smooth
import Submission.Lib.K4QuadraticSheetsReal

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial Metric
open scoped ContDiff

/-- Restrict a real test to hidden coordinate zero. -/
def zeroHiddenPolynomial (P : Poly) : MvPolynomial (Fin 3) ℝ :=
  aeval (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X) P

theorem zeroHiddenPolynomial_totalDegree (P : Poly) :
    (zeroHiddenPolynomial P).totalDegree ≤ P.totalDegree := by
  apply k4_eligibility_sign_description.degree_aeval_le
  intro i
  refine Fin.lastCases ?_ (fun j => by simp) i
  change (0 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1
  simp

theorem eval_complex_zeroHiddenPolynomial (P : Poly) (z : Fin 3 → ℂ) :
    eval z ((zeroHiddenPolynomial P).map (algebraMap ℝ ℂ)) =
      eval (Fin.snoc z 0) (P.map (algebraMap ℝ ℂ)) := by
  exact Submission.Lib.K4QuadraticSheetsReal.eval_map_lastCases_subst P z

theorem HasRealExtension.mono_degree {D D' : ℕ} (hDD : D ≤ D')
    {f : Base → ℝ} (hf : HasRealExtension D f) : HasRealExtension D' f := by
  obtain ⟨F, P, hPne, hPdeg, hF, hrel, hmatch⟩ := hf
  exact ⟨F, P, hPne, hPdeg.trans hDD, hF, hrel, hmatch⟩

/-- Expose the residual's actual rational presentation, including preservation
of a nonzero denominator at each line anchor. The same presentation supplies
both algebraic jet extensions and the one-dimensional norming estimates. -/
theorem quadratic_residual_rational_presentation (D : ℕ) (hD : 2 ≤ D)
    (Δ U V W : MvPolynomial (Fin 3) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hWne : W ≠ 0)
    (s F : EuclideanSpace ℂ (Fin 3) → ℂ)
    (hF : ContDiffOn ℂ ⊤ F (ball 0 4))
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) W * F z =
        eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (f : Base → ℝ)
    (hfF : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ))
    (S : Poly) (hS : S.totalDegree ≤ 2) (a : ℝ) (ha : a ≠ 0) :
    ∃ (UQ VQ WQ : MvPolynomial (Fin 3) ℂ) (Q : EuclideanSpace ℂ (Fin 3) → ℂ),
      UQ.totalDegree ≤ 4 * D ∧ VQ.totalDegree ≤ 4 * D ∧ WQ.totalDegree ≤ 4 * D ∧
      WQ ≠ 0 ∧ ContDiffOn ℂ ⊤ Q (ball 0 4) ∧
      (∀ x ∈ ball (0 : Base) 4, Q (DenseJet.realSlice x) =
        ((eval (Fin.snoc (fun i => x i) (f x)) S / a : ℝ) : ℂ)) ∧
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) WQ * Q z =
          eval (fun i => z i) UQ + eval (fun i => z i) VQ * s z) ∧
      ∀ z : EuclideanSpace ℂ (Fin 3), eval (fun i => z i) W ≠ 0 →
        eval (fun i => z i) WQ ≠ 0 := by
  let SC := S.map (algebraMap ℝ ℂ)
  let A : MvPolynomial (Fin 3) ℂ := C (Submission.Lib.K4QuadraticSheets.qc SC / 2)
  let B := (zeroHiddenPolynomial (pderiv (Fin.last 3) S)).map (algebraMap ℝ ℂ)
  let C₀ := (zeroHiddenPolynomial S).map (algebraMap ℝ ℂ)
  let Q : EuclideanSpace ℂ (Fin 3) → ℂ :=
    fun z => eval (Fin.snoc (fun i => z i) (F z)) SC / (a : ℂ)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hSC : SC.totalDegree ≤ 2 :=
    (Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ S).trans hS
  have hA : A.totalDegree ≤ D := by simp [A]
  have hB : B.totalDegree ≤ D :=
    (Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ _).trans
      ((zeroHiddenPolynomial_totalDegree _).trans
        ((Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' S _
          (d := 1) hS).trans (by omega)))
  have hC : C₀.totalDegree ≤ D :=
    (Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ _).trans
      ((zeroHiddenPolynomial_totalDegree S).trans (hS.trans hD))
  have hQ : ContDiffOn ℂ ⊤ Q (ball 0 4) := by
    apply ContDiffOn.div_const
    apply k4_quadratic_sheet_continuation.contDiffOn_polynomial_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hF
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have hQreal : ∀ x ∈ ball (0 : Base) 4,
      Q (DenseJet.realSlice x) =
        ((eval (Fin.snoc (fun i => x i) (f x)) S / a : ℝ) : ℂ) := by
    intro x hx
    change eval (Fin.snoc (fun i => (x i : ℂ)) (F (DenseJet.realSlice x))) SC / (a : ℂ) = _
    rw [hfF x hx, ← Submission.Lib.K4QuadraticSheetsReal.snoc_ofReal]
    rw [Submission.Lib.K4QuadraticSheetsReal.eval_map_real]
    simp only [Complex.ofReal_div]
  have hquad : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (a : ℂ) * Q z = eval (fun i => z i) A * (F z) ^ 2 +
        eval (fun i => z i) B * F z + eval (fun i => z i) C₀ := by
    intro z _
    dsimp [Q]
    rw [mul_div_cancel₀ _ haC]
    rw [Submission.Lib.K4QuadraticSheets.eval_snoc_quadratic SC hSC]
    dsimp [A, B, C₀]
    rw [eval_C, eval_complex_zeroHiddenPolynomial, eval_complex_zeroHiddenPolynomial]
    simp only [← pderiv_map, Submission.Lib.K4QuadraticSheets.qb,
      Submission.Lib.K4QuadraticSheets.qg, SC]
    have hlast : (Fin.last 3 : Fin 4) = 3 := rfl
    simp only [hlast]
    ring
  obtain ⟨hUQ, hVQ, hWQ⟩ :=
    sqrtRationalQuadratic_degrees D Δ U V W A B C₀ (a : ℂ) hΔ hU hV hW hA hB hC
  refine ⟨sqrtRationalQuadraticU Δ U V W A B C₀,
    sqrtRationalQuadraticV U V W A B, sqrtRationalQuadraticW (a : ℂ) W, Q,
    hUQ, hVQ, hWQ, sqrtRationalQuadraticW_ne_zero _ W haC hWne, hQ, hQreal, ?_, ?_⟩
  · intro z hz
    exact eval_sqrtRationalQuadratic Δ U V W A B C₀ (a : ℂ) (fun i => z i)
      (s z) (F z) (Q z) (hroot z hz) (hrep z hz) (hquad z hz)
  · intro z hz
    simp only [sqrtRationalQuadraticW, map_mul, eval_C, map_pow]
    exact mul_ne_zero haC (pow_ne_zero 2 hz)

/-- All directional jets of an arbitrary normalized quadratic residual
have the exact real algebraic extension required by `SampledBranchData`.
This reuses the common residual presentation and smooth evaluation. -/
theorem hasRealExtension_quadratic_residual_jet (D : ℕ) (hD : 2 ≤ D)
    (Δ U V W : MvPolynomial (Fin 3) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0)
    (s F : EuclideanSpace ℂ (Fin 3) → ℂ)
    (hs : DifferentiableOn ℂ s (ball 0 4))
    (hF : ContDiffOn ℂ ⊤ F (ball 0 4))
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) W * F z =
        eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (f : Base → ℝ)
    (hfF : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ))
    (S : Poly) (hS : S.totalDegree ≤ 2) (a : ℝ) (ha : a ≠ 0)
    (v : Base) (k : ℕ) :
    HasRealExtension (8 * (3 ^ k * (4 * D)) + 2)
      (fun x => iteratedFDeriv ℝ k
        (fun y => eval (Fin.snoc (fun i => y i) (f y)) S / a) x (fun _ => v)) := by
  obtain ⟨UQ, VQ, WQ, Q, hUQ, hVQ, hWQ, hWQne, hQ, hQreal, hrepQ, _⟩ :=
    quadratic_residual_rational_presentation D hD Δ U V W hΔ hU hV hW hWne s F hF
      hroot hrep f hfF S hS a ha
  exact hasRealExtension_rational_directional_jet (4 * D) Δ UQ VQ WQ
    (hΔ.trans (by omega)) hUQ hVQ hWQ hΔne hWQne s Q hs hQ hroot hrepQ
    (fun y => eval (Fin.snoc (fun i => y i) (f y)) S / a) hQreal v k

/-- One uniform degree, selected from the initial rational presentation,
supplies all four extension fields of a sampled branch. The directions
and the coefficients of the real quadratic test do not affect this degree. -/
theorem rational_branch_all_sampled_extensions (D : ℕ) (hD : 2 ≤ D)
    (Δ U V W : MvPolynomial (Fin 3) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0)
    (s F : EuclideanSpace ℂ (Fin 3) → ℂ)
    (hs : DifferentiableOn ℂ s (ball 0 4))
    (hF : ContDiffOn ℂ ⊤ F (ball 0 4))
    (hroot : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (fun i => z i) W * F z =
        eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (f : Base → ℝ)
    (hfF : ∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ))
    (S : Poly) (hS : S.totalDegree ≤ 2) (a : ℝ) (ha : a ≠ 0) :
    HasRealExtension (864 * D + 2) f ∧
    (∀ v : Base, HasRealExtension (864 * D + 2)
      (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
    HasRealExtension (864 * D + 2)
      (fun x => eval ![x 0, x 1, x 2, f x] S / a) ∧
    (∀ v : Base, HasRealExtension (864 * D + 2)
      (fun x => iteratedFDeriv ℝ 3
        (fun y => eval ![y 0, y 1, y 2, f y] S / a) x (fun _ => v))) := by
  have hfjet := hasRealExtension_rational_directional_jet D Δ U V W hΔ hU hV hW
    hΔne hWne s F hs hF hroot hrep f hfF
  have hqjet := hasRealExtension_quadratic_residual_jet D hD Δ U V W hΔ hU hV hW
    hΔne hWne s F hs hF hroot hrep f hfF S hS a ha
  have hqarray : (fun y : Base => eval (Fin.snoc (fun i => y i) (f y)) S / a) =
      (fun y : Base => eval ![y 0, y 1, y 2, f y] S / a) := by
    funext y
    have hcoord : Fin.snoc (fun i => y i) (f y) = ![y 0, y 1, y 2, f y] := by
      funext i
      fin_cases i <;> rfl
    rw [hcoord]
  rw [← hqarray]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hfjet 0 0).mono_degree (by norm_num; omega)
  · intro v
    exact (hfjet v 2).mono_degree (by norm_num; omega)
  · exact (hqjet 0 0).mono_degree (by norm_num; omega)
  · intro v
    exact (hqjet v 3).mono_degree (by norm_num; omega)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
