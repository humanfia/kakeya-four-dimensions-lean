-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/LocalRestoration.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/LocalRestoration.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/LocalRestoration.lean
-- Earlier source attributions below are retained.
import Mathlib

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

/-- The local restoration hypothesis, exactly as frozen in o143. -/
def LocalRestorationAssertion : Prop := (((fun (ev : MvPolynomial (Fin 4) ℝ → (EuclideanSpace ℝ (Fin 3)) → ℝ → ℝ) (dw : MvPolynomial (Fin 4) ℝ → MvPolynomial (Fin 4) ℝ) => ∃ C : ℕ, 1 ≤ C ∧ ∀ (A Z a b h s : ℝ) (S : MvPolynomial (Fin 4) ℝ) (f : (EuclideanSpace ℝ (Fin 3)) → ℝ) (p : Fin 7 → (EuclideanSpace ℝ (Fin 3))), 2 ≤ A → A ≤ Z → 0 < b → b ≤ a → a ≤ 1 → 0 < h → h * A ^ C ≤ b / a → 0 ≤ s → b⁻¹ ≤ Z → S.totalDegree ≤ 2 → (∀ e, |S.coeff e| ≤ Z) → (∀ u w, |ev (dw (dw S)) u w| ≤ A / a) → ContDiffOn ℝ 6 f (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) 3) → |f 0| ≤ Z → ‖fderiv ℝ f 0‖ ≤ Z → ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z → (∀ (c : ℝ) (L : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ), ∃ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1, s ≤ |f u - c - L u|) → (∀ j : ℕ, 2 ≤ j → j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j f u‖ ≤ A * s) → (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) → (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) → (∀ i : Fin 7, ∀ j : ℕ, j ≤ 1 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ ≤ A * (b + s * h)) → ((fun R : (EuclideanSpace ℝ (Fin 3)) → ℝ => (∀ j : ℕ, j ≤ 6 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j R u‖ ≤ A) ∧ (∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 → ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 2, ‖iteratedFDeriv ℝ j (fun v : (EuclideanSpace ℝ (Fin 3)) => iteratedFDeriv ℝ 3 R v (fun _ => p i)) u‖ ≤ A * b / a)) (fun u => ev S u (f u) / a)) → ∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ Z ^ C) ∧ ∀ u ∈ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1, ∀ w : ℝ, |w - f u| ≤ A * b → A⁻¹ ≤ |ev (dw S) u w| → |ev (dw S) u w| ≤ A → |ev Q u w| ≤ A ^ C * b ∧ A ^ (-(C : ℤ)) ≤ |ev (dw Q) u w| ∧ |ev (dw Q) u w| ≤ A ^ C ∧ |ev (dw (dw Q)) u w| ≤ A ^ C / b) (fun (P : MvPolynomial (Fin 4) ℝ) (u : (EuclideanSpace ℝ (Fin 3))) (w : ℝ) => MvPolynomial.eval ![u 0, u 1, u 2, w] P) (fun P : MvPolynomial (Fin 4) ℝ => MvPolynomial.pderiv (3 : Fin 4) P)))

/-- Data on the fixed three-dimensional ball to which local restoration applies. -/
structure LocalBranchData (C : ℕ) where
  A : ℝ
  Z : ℝ
  a : ℝ
  b : ℝ
  h : ℝ
  s : ℝ
  S : MvPolynomial (Fin 4) ℝ
  f : EuclideanSpace ℝ (Fin 3) → ℝ
  p : Fin 7 → EuclideanSpace ℝ (Fin 3)
  two_le_A : 2 ≤ A
  A_le_Z : A ≤ Z
  b_pos : 0 < b
  b_le_a : b ≤ a
  a_le_one : a ≤ 1
  h_pos : 0 < h
  small_scale : h * A ^ C ≤ b / a
  s_nonneg : 0 ≤ s
  inv_b_le_Z : b⁻¹ ≤ Z
  S_degree : S.totalDegree ≤ 2
  S_coeff : ∀ e, |S.coeff e| ≤ Z
  S_curvature : ∀ u : EuclideanSpace ℝ (Fin 3), ∀ w : ℝ,
    |eval ![u 0, u 1, u 2, w] (pderiv 3 (pderiv 3 S))| ≤ A / a
  smooth : ContDiffOn ℝ 6 f (Metric.ball 0 3)
  value_zero : |f 0| ≤ Z
  first_zero : ‖fderiv ℝ f 0‖ ≤ Z
  second_zero : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z
  affine_distance : ∀ (c : ℝ) (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ),
    ∃ u ∈ Metric.closedBall 0 1, s ≤ |f u - c - L u|
  higher_bounds : ∀ j : ℕ, 2 ≤ j → j ≤ 6 →
    ∀ u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖iteratedFDeriv ℝ j f u‖ ≤ A * s
  directions : ∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A
  transverse : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
    A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|
  second_tests : ∀ i : Fin 7, ∀ j : ℕ, j ≤ 1 →
    ∀ u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖iteratedFDeriv ℝ j
        (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i)) u‖ ≤ A * (b + s * h)
  residual_bounds : ∀ j : ℕ, j ≤ 6 →
    ∀ u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖iteratedFDeriv ℝ j
        (fun v => eval ![v 0, v 1, v 2, f v] S / a) u‖ ≤ A
  third_tests : ∀ i : Fin 7, ∀ j : ℕ, j ≤ 2 →
    ∀ u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖iteratedFDeriv ℝ j (fun v => iteratedFDeriv ℝ 3
        (fun z => eval ![z 0, z 1, z 2, f z] S / a) v (fun _ => p i)) u‖ ≤ A * b / a

/-- The subset of normalized points on which the restored test is guaranteed. -/
def LocalBranchData.region {C : ℕ} (D : LocalBranchData C) :
    Set (EuclideanSpace ℝ (Fin 3) × ℝ) :=
  {z | z.1 ∈ Metric.closedBall 0 1 ∧ |z.2 - D.f z.1| ≤ D.A * D.b ∧
    D.A⁻¹ ≤ |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 D.S)| ∧
    |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 D.S)| ≤ D.A}

/-- Quantitative bounds returned by local restoration, before returning to physical units. -/
def LocalBranchData.restored {C : ℕ} (D : LocalBranchData C)
    (Q : MvPolynomial (Fin 4) ℝ) : Prop :=
  Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ D.Z ^ C) ∧
    ∀ z ∈ D.region,
      |eval ![z.1 0, z.1 1, z.1 2, z.2] Q| ≤ D.A ^ C * D.b ∧
      D.A ^ (-(C : ℤ)) ≤ |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 Q)| ∧
      |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 Q)| ≤ D.A ^ C ∧
      |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 (pderiv 3 Q))| ≤ D.A ^ C / D.b

/-- The universal exponent is chosen before any branch, scale, or direction data. -/
theorem apply_local_restoration (h : LocalRestorationAssertion) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ D : LocalBranchData C, ∃ Q, D.restored Q := by
  obtain ⟨C, hC, hr⟩ := h
  refine ⟨C, hC, fun D => ?_⟩
  obtain ⟨Q, hdeg, hcoeff, hQ⟩ := hr D.A D.Z D.a D.b D.h D.s D.S D.f D.p
    D.two_le_A D.A_le_Z D.b_pos D.b_le_a D.a_le_one D.h_pos D.small_scale
    D.s_nonneg D.inv_b_le_Z D.S_degree D.S_coeff D.S_curvature D.smooth
    D.value_zero D.first_zero D.second_zero D.affine_distance D.higher_bounds
    D.directions D.transverse D.second_tests ⟨D.residual_bounds, D.third_tests⟩
  refine ⟨Q, hdeg, hcoeff, ?_⟩
  intro z hz
  exact hQ z.1 hz.1 z.2 hz.2.1 hz.2.2.1 hz.2.2.2

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
