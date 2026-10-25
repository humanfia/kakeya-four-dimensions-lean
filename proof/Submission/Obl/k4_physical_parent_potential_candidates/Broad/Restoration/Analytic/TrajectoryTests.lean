-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/TrajectoryTests.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/TrajectoryTests.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/TrajectoryTests.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.WitnessComparison
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.QuadraticRealJets

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MvPolynomial MeasureTheory
open scoped ContDiff ENNReal

/-- The same tube witnesses bound the physical branch jets from order two
onwards. Only the affine hidden trajectory is subtracted here. -/
theorem branch_jets_of_long_affine_tube
    (hR : DenseJet.SheetRemezAssertion) (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) → ContDiffOn ℝ ∞ f (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (A b : ℝ), 2 ≤ A → 0 ≤ b →
      ∀ (u p : Base) (w₀ w₁ : ℝ), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (E : Set ℝ) (θ : ℝ), MeasurableSet E → E ⊆ Icc (-1) 1 →
        0 < θ → θ ≤ 1 → ENNReal.ofReal θ ≤ volume E →
        (∀ t ∈ E, |w₀ + w₁ * t - f (u + t • ((8 * A)⁻¹ • p))| ≤ A * b) →
        ∀ k : ℕ, 2 ≤ k → k ≤ 6 →
          |iteratedFDeriv ℝ k f u (fun _ => p)| ≤ K * θ ^ (-C) * A ^ 25 * b := by
  obtain ⟨K, C, hK, hC, hnorm⟩ := directional_jet_bound_rational_physical hR D
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hf hmatch A b hA hb
    u p w₀ w₁ hu hp hWa E θ hE hEsub hθ hθ1 hvol hdist k hk2 hk6
  have hmatch' : ∀ x : Base, ‖x‖ < 4 → F (DenseJet.realSlice x) = (f x : ℂ) := by
    intro x hx
    exact hmatch x (by simpa only [mem_ball, dist_zero_right] using hx)
  have hfit : ∀ t ∈ E, |f (u + t • ((8 * A)⁻¹ • p)) - w₀ - w₁ * t| ≤ A * b := by
    intro t ht
    rw [show f (u + t • ((8 * A)⁻¹ • p)) - w₀ - w₁ * t =
      -(w₀ + w₁ * t - f (u + t • ((8 * A)⁻¹ • p))) by ring, abs_neg]
    exact hdist t ht
  have hh := hnorm Δ U V W hΔ hU hV hW s F f hroot hrep (hF.of_le le_top) hf hmatch'
    A hA u p w₀ w₁ hu hp hWa E θ (A * b) hE hEsub hθ hθ1 (by positivity) hvol hfit k hk2 hk6
  exact hh.trans_eq (by ring)

/-- Long actual affine-trajectory tube witnesses give the physical residual
third-jet tests. The old quadratic, its coefficients and all witnesses are
chosen after the uniform norming constants. -/
theorem residual_jets_of_long_affine_tube
    (hR : DenseJet.SheetRemezAssertion) (D : ℕ) (hD : 2 ≤ D) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D → W ≠ 0 →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : Base → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ⊤ F (ball 0 4) → ContDiffOn ℝ ∞ f (ball 0 4) →
      (∀ x ∈ ball (0 : Base) 4, F (DenseJet.realSlice x) = (f x : ℂ)) →
      ∀ (S : Poly), S.totalDegree ≤ 2 → ∀ (A a b : ℝ),
      2 ≤ A → 0 < a → 0 ≤ b → b ≤ a →
      ∀ (u p : Base) (w₀ w₁ : ℝ), u ∈ closedBall (0 : Base) 1 → ‖p‖ ≤ A →
      eval (fun i => (DenseJet.realSlice u) i) W ≠ 0 →
      ∀ (E : Set ℝ) (θ : ℝ), MeasurableSet E → E ⊆ Icc (-1) 1 →
        0 < θ → θ ≤ 1 → ENNReal.ofReal θ ≤ volume E →
        (∀ t ∈ E, |w₀ + w₁ * t - f (u + t • ((8 * A)⁻¹ • p))| ≤ A * b) →
        (∀ t ∈ E,
          |eval ![(u + t • ((8 * A)⁻¹ • p)) 0, (u + t • ((8 * A)⁻¹ • p)) 1,
            (u + t • ((8 * A)⁻¹ • p)) 2, w₀ + w₁ * t] (pderiv 3 S)| ≤ A) →
        (∀ t ∈ E,
          |eval ![(u + t • ((8 * A)⁻¹ • p)) 0, (u + t • ((8 * A)⁻¹ • p)) 1,
            (u + t • ((8 * A)⁻¹ • p)) 2, w₀ + w₁ * t] (pderiv 3 (pderiv 3 S))| ≤ A / a) →
        ∀ k : ℕ, 3 ≤ k → k ≤ 6 →
          |iteratedFDeriv ℝ k (fun x => eval ![x 0, x 1, x 2, f x] S / a)
            u (fun _ => p)| ≤ K * θ ^ (-C) * A ^ 28 * b / a := by
  obtain ⟨K, C, hK, hC, hnorm⟩ := quadratic_fit_physical_norming hR (4 * D)
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW hWne s F f hroot hrep hF hf hmatch S hS A a b hA ha hb hba
    u p w₀ w₁ hu hp hWa E θ hE hEsub hθ hθ1 hvol hdist hfirst hsecond k hk3 hk6
  obtain ⟨UQ, VQ, WQ, Q, hUQ, hVQ, hWQ, hWQne, hQ, hQreal, hrepQ, hQden⟩ :=
    quadratic_residual_rational_presentation D hD Δ U V W hΔ hU hV hW hWne s F hF
      hroot hrep f hmatch S hS a ha.ne'
  let q : Base → ℝ := fun x => eval ![x 0, x 1, x 2, f x] S / a
  have hcoords : ∀ x : Base, Fin.snoc (fun i => x i) (f x) = ![x 0, x 1, x 2, f x] := by
    intro x
    funext i
    fin_cases i <;> rfl
  have hq : ContDiffOn ℝ ∞ q (ball 0 4) := by
    simpa only [q, Submission.Obl.k4_seven_direction_local_degree_restoration.evalAt] using
      Submission.Obl.k4_seven_direction_local_degree_restoration.normalizedGraph_contDiffOn hf S a
  have hQmatch : ∀ x : Base, ‖x‖ < 4 → Q (DenseJet.realSlice x) = (q x : ℂ) := by
    intro x hx
    simpa only [hcoords, q] using hQreal x (by simpa only [mem_ball, dist_zero_right] using hx)
  obtain ⟨α, β, γ, hfit⟩ := exists_quadratic_residual_line_fit S hS f u ((8 * A)⁻¹ • p)
    w₀ w₁ E hA ha hb hba hdist hfirst hsecond
  have hh := hnorm Δ UQ VQ WQ (hΔ.trans (by omega)) hUQ hVQ hWQ s Q q hroot hrepQ
    (hQ.of_le le_top) hq hQmatch A hA u p α β γ hu hp (hQden _ hWa)
    E θ (A ^ 4 * b / a) hE hEsub hθ hθ1 (by positivity) hvol hfit k hk3 hk6
  exact hh.trans_eq (by ring)

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
