-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.LocalNativeBranch, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/LocalNativeBranch.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/LocalNativeBranch.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/LocalNativeBranch.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/LocalNativeBranch.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.UniformSignedBranch
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.BaseTranslation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.LocalNativeCoordinates

/-! # Uniform local signed branches of the original native equation -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MvPolynomial Metric
open k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- The rational presentation of an actual native sheet, including a
denominator nonzero throughout the fixed complex comparison domain. -/
def RationalNativePresentation (d : ℕ) (F : EuclideanSpace ℂ (Fin 3) → ℂ) : Prop :=
  ∃ (Δ U V W : MvPolynomial (Fin 3) ℂ) (s : EuclideanSpace ℂ (Fin 3) → ℂ),
    Δ ≠ 0 ∧ W ≠ 0 ∧ Δ.totalDegree ≤ d ∧ U.totalDegree ≤ d ∧
    V.totalDegree ≤ d ∧ W.totalDegree ≤ d ∧ DifferentiableOn ℂ s (ball 0 4) ∧
    ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (s z) ^ 2 = eval (fun j => z j) Δ ∧
      eval (fun j => z j) W * F z = eval (fun j => z j) U + eval (fun j => z j) V * s z ∧
      eval (fun j => z j) W ≠ 0

/-- All branch assertions refer to the ORIGINAL equation P at c+scale*x.
The same fixed degree controls the hidden branch, its second directional
jets, every original quadratic signal, and its third directional jets. -/
def LocalNativeBranchData (D : ℕ) (P : Poly) (c : Fin 3 → ℝ) (scale σ : ℝ)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ) : Prop :=
    ContDiffOn ℂ ⊤ F (ball 0 4) ∧ ContDiffOn ℝ 6 f (ball 0 3) ∧
    (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) ∧
    (∀ x ∈ ball (0 : Base) 4,
      eval (Fin.snoc (fun j => c j + scale * x j) (f x)) P = 0 ∧
      0 < eval (Fin.snoc (fun j => c j + scale * x j) (f x)) (pderiv 3 P) * σ) ∧
    RationalNativePresentation 6 F ∧
    HasRealExtension D f ∧
    (∀ v : Base, HasRealExtension D (fun x => iteratedFDeriv ℝ 2 f x (fun _ => v))) ∧
    ∀ (S : Poly) (lam : ℝ), S.totalDegree ≤ 2 → lam ≠ 0 →
      HasRealExtension D
        (fun x => eval (Fin.snoc (fun j => c j + scale * x j) (f x)) S / lam) ∧
      ∀ v : Base, HasRealExtension D
        (fun x => iteratedFDeriv ℝ 3
          (fun y => eval (Fin.snoc (fun j => c j + scale * y j) (f y)) S / lam)
          x (fun _ => v))

/-- A local branch with its chosen complex and real functions. -/
def LocalNativeBranch (D : ℕ) (P : Poly) (c : Fin 3 → ℝ) (scale σ : ℝ) : Prop :=
  ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
    LocalNativeBranchData D P c scale σ F f

/-- The radius exponent and relation degree are fixed before every
coefficient, original source law, and input format. Only the discriminant
height is used; P's other coefficients can be arbitrarily large. -/
theorem uniform_centered_native_branch :
    ∃ E : ℕ, 1 ≤ E ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ (P : Poly), P.totalDegree ≤ 2 →
      ∀ c : Fin 3 → ℝ, (∀ j, |c j| ≤ 1) →
      (∀ d, |(baseDiscriminant P).coeff d| ≤ A) →
      (A⁻¹) ^ 2 ≤ eval c (baseDiscriminant P) →
      ∀ σ : ℝ, σ ≠ 0 →
      (curvature P 3 = 0 → 0 < eval c (restrictBase (pderiv 3 P)) * σ) →
      LocalNativeBranch (864 * (2 * (2 + 1)) + 2) P c (A ^ E)⁻¹ σ := by
  obtain ⟨q, hq, hcentered⟩ := centered_native_discriminant_preparation 2
  obtain ⟨M, hM, hbranch⟩ := uniform_signed_branch_with_extensions 2
  refine ⟨q * M, by nlinarith, ?_⟩
  intro A hA P hP c hc hcoeff hfloor σ hσ hσ0
  let B : MvPolynomial (Fin 3) ℝ := restrictBase (pderiv 3 P)
  let C₀ : MvPolynomial (Fin 3) ℝ := restrictBase P
  let a : ℝ := curvature P 3 / 2
  have hB : B.totalDegree ≤ 2 := (er_totalDegree_restrict_deriv P hP).trans (by omega)
  have hC : C₀.totalDegree ≤ 2 := er_totalDegree_restrict P hP
  have hdisc : nativeBaseDiscriminant a B C₀ = baseDiscriminant P :=
    (native_equation_discriminant P).symm
  obtain ⟨hBc, hCc, hcoeffc, hfloorc⟩ := hcentered A hA B C₀ a c hB hC hc
    (by simpa only [hdisc] using hcoeff) (by simpa only [hdisc] using hfloor)
  have hAq : 2 ≤ A ^ q := hA.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ A) hq)
  obtain ⟨F, f, hF, hf, hreal, hcomplex, hroot, hext⟩ :=
    hbranch (A ^ q) hAq (baseTranslation c B) (baseTranslation c C₀) a σ
      hBc hCc hσ (by
        intro ha
        have hc0 : curvature P 3 = 0 := by dsimp only [a] at ha; linarith
        simpa only [eval_baseTranslation, add_zero] using hσ0 hc0)
      hcoeffc hfloorc
  let Bδ := baseDilation ((A ^ q) ^ M)⁻¹ (baseTranslation c B)
  let Cδ := baseDilation ((A ^ q) ^ M)⁻¹ (baseTranslation c C₀)
  have hBδ : (Bδ.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 :=
    ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ Bδ).trans
      (baseDilation_totalDegree _ _)).trans hBc
  have hCδ : (Cδ.map (algebraMap ℝ ℂ)).totalDegree ≤ 2 :=
    ((Submission.Lib.K4QuadraticSheetsReal.totalDegree_map_le' _ Cδ).trans
      (baseDilation_totalDegree _ _)).trans hCc
  obtain ⟨Δ, U, V, W, hΔne, hWne, hΔ, hU, hV, hW, hpresentation⟩ :=
    presentation_of_simple_quadratic_branch 2 (Bδ.map (algebraMap ℝ ℂ))
      (Cδ.map (algebraMap ℝ ℂ)) hBδ hCδ (a : ℂ) (ball 0 4) (by simp)
      F (fun z hz => (hcomplex z hz).1) (fun z hz => (hcomplex z hz).2)
  let s : EuclideanSpace ℂ (Fin 3) → ℂ := fun z =>
    eval (fun j => z j) (Bδ.map (algebraMap ℝ ℂ)) + 2 * (a : ℂ) * F z
  have hs : DifferentiableOn ℂ s (ball 0 4) := by
    have hpoly : ContDiffOn ℂ ⊤
        (fun z : EuclideanSpace ℂ (Fin 3) => eval (fun j => z j) (Bδ.map (algebraMap ℝ ℂ)))
        (ball 0 4) := by
      apply k4_quadratic_sheet_continuation.contDiffOn_polynomial_eval
      intro j
      fun_prop
    exact (hpoly.add ((contDiffOn_const : ContDiffOn ℂ ⊤
      (fun _ : EuclideanSpace ℂ (Fin 3) => 2 * (a : ℂ)) (ball 0 4)).mul hF)).differentiableOn
      (by simp)
  have hBval (x : Base) :
      eval (fun j => x j) (baseDilation ((A ^ q) ^ M)⁻¹ (baseTranslation c B)) =
        eval (fun j => c j + (A ^ (q * M))⁻¹ * x j) B := by
    simp only [eval_baseDilation, eval_baseTranslation, ← pow_mul]
  have hCval (x : Base) :
      eval (fun j => x j) (baseDilation ((A ^ q) ^ M)⁻¹ (baseTranslation c C₀)) =
        eval (fun j => c j + (A ^ (q * M))⁻¹ * x j) C₀ := by
    simp only [eval_baseDilation, eval_baseTranslation, ← pow_mul]
  have he0 := hext 0 1 (by simp) (by norm_num)
  refine ⟨F, f, hF, hf, hreal, ?_, ?_, he0.1, he0.2.1, ?_⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [eval_snoc_quadratic P hP]
      change eval (fun j => c j + (A ^ (q * M))⁻¹ * x j) C₀ +
        eval (fun j => c j + (A ^ (q * M))⁻¹ * x j) B * f x +
        curvature P 3 * (f x) ^ 2 / 2 = 0
      rw [← hBval x, ← hCval x]
      have hh := (hroot x hx).1
      dsimp only [a] at hh
      linear_combination hh
    · rw [native_equation_derivative P hP]
      change 0 < (2 * a * f x +
        eval (fun j => c j + (A ^ (q * M))⁻¹ * x j) B) * σ
      rw [← hBval x]
      exact (hroot x hx).2
  · exact ⟨Δ, U, V, W, s, hΔne, hWne, hΔ, hU, hV, hW, hs, hpresentation⟩
  · intro S lam hS hlam
    let S' := localNativePolynomial c (A ^ (q * M))⁻¹ S
    have hS' : S'.totalDegree ≤ 2 := (localNativePolynomial_totalDegree _ _ S).trans hS
    obtain ⟨_, _, hsignal, hthird⟩ := hext S' lam hS' hlam
    have heq : (fun x : Base => eval ![x 0, x 1, x 2, f x] S' / lam) =
        (fun x : Base => eval
          (Fin.snoc (fun j => c j + (A ^ (q * M))⁻¹ * x j) (f x)) S / lam) := by
      funext x
      exact congrArg (fun v : ℝ => v / lam) (localNativePolynomial_eval c _ S x (f x))
    rw [heq] at hsignal hthird
    exact ⟨hsignal, hthird⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
