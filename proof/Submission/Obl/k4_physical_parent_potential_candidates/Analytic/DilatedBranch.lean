-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/DilatedBranch.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/DilatedBranch.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/DilatedBranch.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.SmallDilation
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RealStableBranch
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.PolyAlgebra

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

def baseDilation {n : ℕ} (s : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := bind₁ (fun i => C s * X i) P

theorem baseDilation_totalDegree {n : ℕ} (s : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    (baseDilation s P).totalDegree ≤ P.totalDegree := by
  apply k4_remainder_pure_profile_normalization.Normalization.totalDegree_bind₁_le_of_le_one
  intro i
  exact (totalDegree_mul _ _).trans (by simp)

theorem eval_baseDilation {n : ℕ} (s : ℝ) (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (baseDilation s P) = eval (fun i => s * x i) P := by
  change eval₂Hom (RingHom.id ℝ) _ (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin n → ℝ => eval₂Hom (RingHom.id ℝ) f P)
  funext i
  simp

theorem eval_complex_baseDilation {n : ℕ} (s : ℝ) (P : MvPolynomial (Fin n) ℝ)
    (z : EuclideanSpace ℂ (Fin n)) :
    eval (fun i => z i) ((baseDilation s P).map (algebraMap ℝ ℂ)) =
      eval (fun i => (s : ℂ) * z i) (P.map (algebraMap ℝ ℂ)) := by
  rw [← eval₂_eq_eval_map, ← eval₂_eq_eval_map]
  change eval₂Hom (algebraMap ℝ ℂ) _ (bind₁ _ P) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin n → ℂ => eval₂Hom (algebraMap ℝ ℂ) f P)
  funext i
  simp

def nativeBaseDiscriminant {n : ℕ} (a : ℝ) (B C₀ : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ := B ^ 2 - C (4 * a) * C₀

theorem nativeBaseDiscriminant_totalDegree {n : ℕ} (d : ℕ) (a : ℝ)
    (B C₀ : MvPolynomial (Fin n) ℝ) (hB : B.totalDegree ≤ d) (hC : C₀.totalDegree ≤ d) :
    (nativeBaseDiscriminant a B C₀).totalDegree ≤ 2 * d := by
  apply (totalDegree_sub _ _).trans
  refine max_le ((totalDegree_pow B 2).trans (Nat.mul_le_mul_left 2 hB)) ?_
  apply (totalDegree_mul _ _).trans
  simpa only [totalDegree_C, zero_add] using hC.trans (by omega : d ≤ 2 * d)

theorem eval_complex_nativeBaseDiscriminant {n : ℕ} (a : ℝ)
    (B C₀ : MvPolynomial (Fin n) ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    eval (fun i => z i) ((nativeBaseDiscriminant a B C₀).map (algebraMap ℝ ℂ)) =
      (eval (fun i => z i) (B.map (algebraMap ℝ ℂ))) ^ 2 -
        4 * (a : ℂ) * eval (fun i => z i) (C₀.map (algebraMap ℝ ℂ)) := by
  simp [nativeBaseDiscriminant]

theorem baseDilation_nativeBaseDiscriminant {n : ℕ} (s a : ℝ)
    (B C₀ : MvPolynomial (Fin n) ℝ) :
    baseDilation s (nativeBaseDiscriminant a B C₀) =
      nativeBaseDiscriminant a (baseDilation s B) (baseDilation s C₀) := by
  simp [baseDilation, nativeBaseDiscriminant]

/-- The exponent is fixed before all coefficient and branch data. After
this actual real-polynomial dilation, the two conclusions are exactly the
comparison margins used by `exists_real_stable_branch_with_extensions`.
The polynomial degrees are preserved by `baseDilation_totalDegree`. -/
theorem native_branch_margins_after_uniform_dilation (d : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ A : ℝ, 2 ≤ A →
      ∀ (B C₀ : MvPolynomial (Fin 3) ℝ) (a : ℝ),
      B.totalDegree ≤ d → C₀.totalDegree ≤ d →
      (∀ m, |B.coeff m| ≤ A) → (∀ m, |(nativeBaseDiscriminant a B C₀).coeff m| ≤ A) →
      ∀ β : ℝ, 0 < β → A⁻¹ ≤ β →
      ‖eval (fun _ => (0 : ℂ)) (B.map (algebraMap ℝ ℂ)) - (β : ℂ)‖ ≤ β / 8 →
      ‖eval (fun _ => (0 : ℂ)) ((nativeBaseDiscriminant a B C₀).map (algebraMap ℝ ℂ)) -
        (β : ℂ) ^ 2‖ ≤ β ^ 2 / 8 →
      ∀ z : EuclideanSpace ℂ (Fin 3), ‖z‖ ≤ 4 →
        ‖eval (fun i => z i) ((baseDilation (A ^ M)⁻¹ B).map (algebraMap ℝ ℂ)) -
          (β : ℂ)‖ ≤ β / 4 ∧
        ‖(eval (fun i => z i) ((baseDilation (A ^ M)⁻¹ B).map (algebraMap ℝ ℂ))) ^ 2 -
          4 * (a : ℂ) * eval (fun i => z i) ((baseDilation (A ^ M)⁻¹ C₀).map (algebraMap ℝ ℂ)) -
            (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4 := by
  obtain ⟨M, hM, hmargins⟩ := comparison_margins_after_small_dilation 3 (2 * d)
  refine ⟨M, hM, ?_⟩
  intro A hA B C₀ a hB hC hBc hRc β hβ hfloor hb0 hr0 z hz
  obtain ⟨hb, hr⟩ := hmargins A hA B (nativeBaseDiscriminant a B C₀)
    (hB.trans (by omega)) (nativeBaseDiscriminant_totalDegree d a B C₀ hB hC)
    hBc hRc β hβ hfloor hb0 hr0 z hz
  have hdilated :
      ‖eval (fun i => z i) ((baseDilation (A ^ M)⁻¹ (nativeBaseDiscriminant a B C₀)).map
        (algebraMap ℝ ℂ)) - (β : ℂ) ^ 2‖ ≤ β ^ 2 / 4 := by
    simpa only [eval_complex_baseDilation, Complex.ofReal_inv, Complex.ofReal_pow,
      PiLp.smul_apply, smul_eq_mul] using hr
  refine ⟨?_, ?_⟩
  · simpa only [eval_complex_baseDilation, Complex.ofReal_inv, Complex.ofReal_pow,
      PiLp.smul_apply, smul_eq_mul] using hb
  · simpa only [baseDilation_nativeBaseDiscriminant, eval_complex_nativeBaseDiscriminant] using hdilated

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
