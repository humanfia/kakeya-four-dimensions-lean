-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/IteratedRational.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/IteratedRational.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/IteratedRational.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.FrechetRational

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial
open scoped ContDiff

/-- Evaluating a fixed tuple in the complex jets preserves analytic
regularity on the original open domain. -/
theorem contDiffOn_complex_jet_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E → ℂ}
    (hF : ContDiffOn ℂ ⊤ F Ω) (k : ℕ) (v : Fin k → E) :
    ContDiffOn ℂ ⊤ (fun z => iteratedFDeriv ℂ k F z v) Ω := by
  intro z hz
  have hj : ContDiffAt ℂ ⊤ (iteratedFDeriv ℂ k F) z :=
    (hF.contDiffAt (hΩ.mem_nhds hz)).iteratedFDeriv_right (by simp)
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => E) ℂ v).contDiff.contDiffAt.comp
    z hj).contDiffWithinAt

/-- The derivative of a constant-direction complex jet is the next jet.
This is the complex-field version of the real helper in this tree's
o180 `Symm.lean`, using Mathlib's multilinear evaluation rule directly. -/
theorem fderiv_complex_jet_apply {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {F : E → ℂ}
    (hF : ContDiffOn ℂ ⊤ F Ω) (k : ℕ) (v : E) {z : E} (hz : z ∈ Ω) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ k F y (fun _ => v)) z v =
      iteratedFDeriv ℂ (k + 1) F z (fun _ => v) := by
  have hj : DifferentiableAt ℂ (iteratedFDeriv ℂ k F) z :=
    (hF.contDiffAt (hΩ.mem_nhds hz)).differentiableAt_iteratedFDeriv (by simp)
  rw [fderiv_continuousMultilinear_apply_const_apply hj, iteratedFDeriv_succ_apply_left]
  rfl

/-- Every constant-direction jet stays in the original quadratic extension.
The degree cost is at most a factor of three per derivative, independent
of the branch, domain, direction, or polynomial coefficients. -/
theorem exists_iterated_rational_presentation {n : ℕ} (D : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0)
    (Ω : Set (EuclideanSpace ℂ (Fin n))) (hΩ : IsOpen Ω)
    (s F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hs : DifferentiableOn ℂ s Ω) (hF : ContDiffOn ℂ ⊤ F Ω)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ Ω, eval (fun i => z i) W * F z =
      eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (v : EuclideanSpace ℂ (Fin n)) (k : ℕ) :
    ∃ U' V' W' : MvPolynomial (Fin n) ℂ,
      W' ≠ 0 ∧ U'.totalDegree ≤ 3 ^ k * D ∧
      V'.totalDegree ≤ 3 ^ k * D ∧ W'.totalDegree ≤ 3 ^ k * D ∧
      ∀ z ∈ Ω, eval (fun i => z i) W' *
        iteratedFDeriv ℂ k F z (fun _ => v) =
          eval (fun i => z i) U' + eval (fun i => z i) V' * s z := by
  induction k with
  | zero =>
    exact ⟨U, V, W, hWne, by simpa using hU, by simpa using hV,
      by simpa using hW, hrep⟩
  | succ k ih =>
    obtain ⟨Uk, Vk, Wk, hWkne, hUk, hVk, hWk, hkrepr⟩ := ih
    let δ := complexPolynomialDirectional (fun i => v i)
    have hδ : ∀ P : MvPolynomial (Fin n) ℂ,
        P.totalDegree ≤ 3 ^ k * D → (δ P).totalDegree ≤ 3 ^ k * D :=
      fun P hP => (complexPolynomialDirectional_totalDegree (fun i => v i) P).trans hP
    have hΔk : Δ.totalDegree ≤ 3 ^ k * D := hΔ.trans (by
      simpa using Nat.mul_le_mul_right D (one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ))))
    obtain ⟨hnextU, hnextV, hnextW⟩ :=
      sqrtRationalNext_degrees (3 ^ k * D) δ hδ Δ Uk Vk Wk hΔk hUk hVk hWk
    refine ⟨sqrtRationalNextU δ Δ Uk Wk, sqrtRationalNextV δ Δ Vk Wk,
      sqrtRationalNextW Δ Wk, sqrtRationalNextW_ne_zero Δ Wk hΔne hWkne,
      ?_, ?_, ?_, ?_⟩
    · simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnextU
    · simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnextV
    · simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnextW
    · intro z hz
      have hj := contDiffOn_complex_jet_apply hΩ hF k (fun _ => v)
      have heq := frechet_sqrtRationalNext Δ Uk Vk Wk v Ω hΩ s
        (fun y => iteratedFDeriv ℂ k F y (fun _ => v)) hs
        (hj.differentiableOn (by simp)) hroot hkrepr z hz
      rw [fderiv_complex_jet_apply hΩ hF k v hz] at heq
      exact heq

/-- A uniform nonzero relation for every actual directional jet. -/
theorem exists_iterated_frechet_relation {n : ℕ} (D : ℕ)
    (Δ U V W : MvPolynomial (Fin n) ℂ)
    (hΔ : Δ.totalDegree ≤ D) (hU : U.totalDegree ≤ D)
    (hV : V.totalDegree ≤ D) (hW : W.totalDegree ≤ D)
    (hΔne : Δ ≠ 0) (hWne : W ≠ 0)
    (Ω : Set (EuclideanSpace ℂ (Fin n))) (hΩ : IsOpen Ω)
    (s F : EuclideanSpace ℂ (Fin n) → ℂ)
    (hs : DifferentiableOn ℂ s Ω) (hF : ContDiffOn ℂ ⊤ F Ω)
    (hroot : ∀ z ∈ Ω, (s z) ^ 2 = eval (fun i => z i) Δ)
    (hrep : ∀ z ∈ Ω, eval (fun i => z i) W * F z =
      eval (fun i => z i) U + eval (fun i => z i) V * s z)
    (v : EuclideanSpace ℂ (Fin n)) (k : ℕ) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ,
      P ≠ 0 ∧ P.totalDegree ≤ 8 * (3 ^ k * D) + 2 ∧
      ∀ z ∈ Ω, eval (Fin.snoc (fun i => z i)
        (iteratedFDeriv ℂ k F z (fun _ => v))) P = 0 := by
  obtain ⟨Uk, Vk, Wk, hWkne, hUk, hVk, hWk, hkrepr⟩ :=
    exists_iterated_rational_presentation D Δ U V W hΔ hU hV hW hΔne hWne
      Ω hΩ s F hs hF hroot hrep v k
  have hΔk : Δ.totalDegree ≤ 3 ^ k * D := hΔ.trans (by
    simpa using Nat.mul_le_mul_right D (one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ))))
  exact exists_sqrt_rational_relation (3 ^ k * D) Δ Uk Vk Wk hWkne hΔk hUk hVk hWk
    Ω (fun z i => z i) s (fun z => iteratedFDeriv ℂ k F z (fun _ => v)) hroot hkrepr

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
