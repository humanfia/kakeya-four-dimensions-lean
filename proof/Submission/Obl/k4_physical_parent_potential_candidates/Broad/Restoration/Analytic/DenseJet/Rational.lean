-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/Analytic/DenseJet/Rational.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/Analytic/DenseJet/Rational.lean (session x0945).
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (with x0491's contributions), branch x0487,
-- commit 36234c36, file Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/Rational.lean
-- (namespace renamed; the attributions that file carries are kept below).
import Mathlib
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.DenseJet.Line
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.LineRestriction

/-!
# The directional estimate for rational square-root branches

For a smooth branch `F = (U + V √Δ) / W` on the radius-four ball, with base polynomials of
degree at most `D` and `W` nonzero at the anchor of a line `a + t v`, closeness to an affine
hidden trajectory on a parameter set of length at least `θ` bounds the derivatives of order
two to six along the line. The one-variable relation comes from x0487's
`LineRestriction.hasSheetRelation_affine_line_error` (this tree, o143, branch x0487).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Line

open Set Metric MeasureTheory MvPolynomial
open Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet
  (SheetRemezAssertion realSlice realSlice_apply norm_realSlice_apply)
open scoped ContDiff ENNReal

theorem directional_jet_bound_rational (hR : SheetRemezAssertion) (D : ℕ) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
    ∀ (Δ U V W : MvPolynomial (Fin 3) ℂ), Δ.totalDegree ≤ D → U.totalDegree ≤ D →
      V.totalDegree ≤ D → W.totalDegree ≤ D →
      ∀ (s F : EuclideanSpace ℂ (Fin 3) → ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (s z) ^ 2 = eval (fun i => z i) Δ) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
        eval (fun i => z i) W * F z = eval (fun i => z i) U + eval (fun i => z i) V * s z) →
      ContDiffOn ℂ ∞ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → F (realSlice x) = (f x : ℂ)) →
      ∀ (a v : EuclideanSpace ℝ (Fin 3)) (α β : ℝ), ‖a‖ + 4 * ‖v‖ < 4 →
      eval (fun i => (realSlice a) i) W ≠ 0 →
      ∀ (S : Set ℝ) (θ ε : ℝ), MeasurableSet S → S ⊆ Icc (-1) 1 → 0 < θ → θ ≤ 1 →
        0 ≤ ε → ENNReal.ofReal θ ≤ volume S →
        (∀ t ∈ S, |f (a + t • v) - α - β * t| ≤ ε) →
        ∀ k : ℕ, 2 ≤ k → k ≤ 6 → ∀ t ∈ Icc (-2 : ℝ) 2,
          |iteratedDeriv k (fun r : ℝ => f (a + r • v)) t| ≤ K * θ ^ (-C) * ε := by
  obtain ⟨K, C, hK, hC, hdir⟩ := directional_jet_bound hR (8 * (D + 1) + 2)
  refine ⟨K, C, hK, hC, ?_⟩
  intro Δ U V W hΔ hU hV hW s F f hroot hrep hF hfF a v α β hav hWa
  have hmap : MapsTo (fun z : EuclideanSpace ℂ (Fin 1) => realSlice a + z 0 • realSlice v)
      (ball 0 4) (ball 0 4) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz ⊢
    have hz0 : ‖z 0‖ ≤ ‖z‖ := by
      have := PiLp.norm_apply_le z 0
      simpa using this
    calc
      ‖realSlice a + z 0 • realSlice v‖ ≤ ‖realSlice a‖ + ‖z 0‖ * ‖realSlice v‖ := by
        simpa only [norm_smul] using norm_add_le (realSlice a) (z 0 • realSlice v)
      _ ≤ ‖a‖ + 4 * ‖v‖ := by
        rw [norm_realSlice_apply, norm_realSlice_apply]
        gcongr
        linarith
      _ < 4 := hav
  have hrel := Submission.Obl.k4_physical_parent_potential_candidates.Analytic.hasSheetRelation_affine_line_error
    D Δ U V W hΔ hU hV hW (ball 0 4) s F hroot hrep (realSlice a) (realSlice v) (α : ℂ) (β : ℂ)
    hWa hmap
  exact hdir F f a v α β hav hF hfF hrel
end Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Line
