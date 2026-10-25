-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.BaseTranslation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/BaseTranslation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/BaseTranslation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/BaseTranslation.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/BaseTranslation.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.CoefficientBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DilatedBranch

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

noncomputable section

open MvPolynomial

def baseTranslation {n : ℕ} (c : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := bind₁ (fun i => C (c i) + X i) P

theorem baseTranslation_totalDegree {n : ℕ} (c : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) :
    (baseTranslation c P).totalDegree ≤ P.totalDegree := by
  apply k4_remainder_pure_profile_normalization.Normalization.totalDegree_bind₁_le_of_le_one
  intro i
  exact (totalDegree_add _ _).trans (max_le (by simp) (by simp))

theorem eval_baseTranslation {n : ℕ} (c : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    eval x (baseTranslation c P) = eval (fun i => c i + x i) P := by
  change eval₂Hom (RingHom.id ℝ) _ (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin n → ℝ => eval₂Hom (RingHom.id ℝ) f P)
  funext i
  simp

theorem eval_complex_baseTranslation {n : ℕ} (c : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℂ) :
    eval x ((baseTranslation c P).map (algebraMap ℝ ℂ)) =
      eval (fun i => (c i : ℂ) + x i) (P.map (algebraMap ℝ ℂ)) := by
  rw [← eval₂_eq_eval_map, ← eval₂_eq_eval_map]
  change eval₂Hom (algebraMap ℝ ℂ) _ (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin n → ℂ => eval₂Hom (algebraMap ℝ ℂ) f P)
  funext i
  simp

theorem baseTranslation_nativeBaseDiscriminant {n : ℕ} (c : Fin n → ℝ) (a : ℝ)
    (B C₀ : MvPolynomial (Fin n) ℝ) :
    baseTranslation c (nativeBaseDiscriminant a B C₀) =
      nativeBaseDiscriminant a (baseTranslation c B) (baseTranslation c C₀) := by
  simp [baseTranslation, nativeBaseDiscriminant]

/-- Moving the center within the unit coordinate box costs a fixed
degree-dependent constant in coefficient height. -/
theorem baseTranslation_coefficient_bound {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ m, |P.coeff m| ≤ A) (c : Fin n → ℝ) (hc : ∀ i, |c i| ≤ 1)
    (m : Fin n →₀ ℕ) :
    |(baseTranslation c P).coeff m| ≤ (((D + 1 : ℕ) : ℝ) ^ n * (2 : ℝ) ^ D) * A := by
  have hcoordinate (i : Fin n) : coefficientMass (C (c i) + X i : MvPolynomial (Fin n) ℝ) ≤ 2 := by
    apply (coefficientMass_add_le _ _).trans
    simpa only [coefficientMass_C, coefficientMass_X] using
      (show |c i| + 1 ≤ 2 by linarith [hc i])
  have hmass : coefficientMass P ≤ ((D + 1 : ℕ) : ℝ) ^ n * A := by
    simpa only [Nat.cast_pow] using coefficientMass_le_of_degree P hP hA hcoeff
  calc
    |(baseTranslation c P).coeff m| ≤ coefficientMass (baseTranslation c P) :=
      abs_coeff_le_coefficientMass _ _
    _ ≤ coefficientMass P * (2 : ℝ) ^ P.totalDegree :=
      coefficientMass_bind_le P _ (by norm_num) hcoordinate
    _ ≤ (((D + 1 : ℕ) : ℝ) ^ n * A) * (2 : ℝ) ^ D :=
      mul_le_mul hmass (pow_le_pow_right₀ (by norm_num) hP) (by positivity) (by positivity)
    _ = _ := by ring

/-- The exponent is chosen before the height, polynomial and center, so
coefficient bounds remain powers of the same parameter after localization. -/
theorem uniform_baseTranslation_coefficient_power_bound (n D : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ P : MvPolynomial (Fin n) ℝ, P.totalDegree ≤ D →
      (∀ m, |P.coeff m| ≤ A) → ∀ c : Fin n → ℝ, (∀ i, |c i| ≤ 1) →
      ∀ m, |(baseTranslation c P).coeff m| ≤ A ^ q := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt
    ((((D + 1 : ℕ) : ℝ) ^ n) * (2 : ℝ) ^ D) (by norm_num : (1 : ℝ) < 2)
  refine ⟨q + 1, by omega, ?_⟩
  intro A hA P hP hcoeff c hc m
  calc
    |(baseTranslation c P).coeff m| ≤ (((D + 1 : ℕ) : ℝ) ^ n * (2 : ℝ) ^ D) * A :=
      baseTranslation_coefficient_bound P hP (by linarith) hcoeff c hc m
    _ ≤ A ^ q * A := mul_le_mul_of_nonneg_right
      (hq.le.trans (pow_le_pow_left₀ (by norm_num) hA _)) (by linarith)
    _ = A ^ (q + 1) := (pow_succ _ _).symm

/-- Moving a good center to zero preserves exactly the degree, coefficient
and central discriminant hypotheses needed for uniform signed branches.
Only the coefficient-height parameter is raised to a fixed power. -/
theorem centered_native_discriminant_preparation (d : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ (B C₀ : MvPolynomial (Fin 3) ℝ) (a : ℝ) (c : Fin 3 → ℝ),
      B.totalDegree ≤ d → C₀.totalDegree ≤ d → (∀ i, |c i| ≤ 1) →
      (∀ m, |(nativeBaseDiscriminant a B C₀).coeff m| ≤ A) →
      (A⁻¹) ^ 2 ≤ eval c (nativeBaseDiscriminant a B C₀) →
      (baseTranslation c B).totalDegree ≤ d ∧ (baseTranslation c C₀).totalDegree ≤ d ∧
      (∀ m, |(nativeBaseDiscriminant a (baseTranslation c B) (baseTranslation c C₀)).coeff m| ≤ A ^ q) ∧
      ((A ^ q)⁻¹) ^ 2 ≤ eval (fun _ => (0 : ℝ))
        (nativeBaseDiscriminant a (baseTranslation c B) (baseTranslation c C₀)) := by
  obtain ⟨q, hq, hcoeffPower⟩ := uniform_baseTranslation_coefficient_power_bound 3 (2 * d)
  refine ⟨q, hq, ?_⟩
  intro A hA B C₀ a c hB hC hc hcoeff hcenter
  have hApos : 0 < A := by linarith
  have hpower : A ≤ A ^ q := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ A) hq
  have hinv : (A ^ q)⁻¹ ≤ A⁻¹ := inv_anti₀ hApos hpower
  refine ⟨(baseTranslation_totalDegree c B).trans hB,
    (baseTranslation_totalDegree c C₀).trans hC, ?_, ?_⟩
  · intro m
    rw [← baseTranslation_nativeBaseDiscriminant]
    exact hcoeffPower A hA (nativeBaseDiscriminant a B C₀)
      (nativeBaseDiscriminant_totalDegree d a B C₀ hB hC) hcoeff c hc m
  · rw [← baseTranslation_nativeBaseDiscriminant, eval_baseTranslation]
    simpa only [add_zero] using
      (pow_le_pow_left₀ (by positivity : 0 ≤ (A ^ q)⁻¹) hinv 2).trans hcenter

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
