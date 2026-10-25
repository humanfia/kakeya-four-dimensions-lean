-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/DiscriminantRemez.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PolynomialRemez

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MvPolynomial MeasureTheory Set Metric

/-- Whole-piece quadratic fit bounds control the hidden discriminant on the base projection. -/
theorem quadratic_discriminant_point_bound {a b c w δ U : ℝ}
    (hδ : 0 < δ) (hU : 0 ≤ U)
    (hvalue : |a * w ^ 2 + b * w + c| ≤ U * δ)
    (hslope : |2 * a * w + b| ≤ U) (hcurv : |2 * a| ≤ U / δ) :
    |b ^ 2 - 4 * a * c| ≤ 3 * U ^ 2 := by
  have heq : b ^ 2 - 4 * a * c =
      (2 * a * w + b) ^ 2 - 2 * (2 * a) * (a * w ^ 2 + b * w + c) := by ring
  rw [heq]
  calc
    _ ≤ |2 * a * w + b| ^ 2 + 2 * |2 * a| * |a * w ^ 2 + b * w + c| := by
      calc
        _ ≤ |(2 * a * w + b) ^ 2| + |2 * (2 * a) * (a * w ^ 2 + b * w + c)| :=
          abs_sub _ _
        _ = _ := by
          rw [abs_pow, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ U ^ 2 + 2 * (U / δ) * (U * δ) := by gcongr
    _ = 3 * U ^ 2 := by field_simp; ring

/-- The coefficient bounds needed by stable hidden sheets follow from a positive-volume
matched projection. The constants are independent of all candidate coefficients. -/
theorem exists_discriminant_coefficient_bound (h : algebraicRemez) :
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
      ∀ (a : ℝ) (b c : MvPolynomial (Fin 3) ℝ),
      b.totalDegree ≤ 1 → c.totalDegree ≤ 2 →
      ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (θ δ U : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 < δ → 0 ≤ U →
      ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤ volume E →
      |2 * a| ≤ U / δ →
      (∀ u ∈ E, ∃ w : ℝ,
        |a * w ^ 2 + eval (fun j => u j) b * w + eval (fun j => u j) c| ≤ U * δ ∧
        |2 * a * w + eval (fun j => u j) b| ≤ U) →
      ∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤
        K * (C * θ ^ (-C) * (3 * U ^ 2)) := by
  obtain ⟨K, C, hK, hC, hbound⟩ := exists_polynomial_remez_coefficient_bound h 3 2
  refine ⟨K, C, hK, hC, ?_⟩
  intro a b c hb hc E θ δ U hE hEsub hθ hθ1 hδ hU hmass hcurv hproj e
  have hdegree : (b * b - MvPolynomial.C (4 * a) * c).totalDegree ≤ 2 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by omega)
    · apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, zero_add]
      exact hc
  apply hbound _ hdegree E θ (3 * U ^ 2) hE hEsub hθ hθ1 (by positivity) hmass
  intro u hu
  obtain ⟨w, hval, hder⟩ := hproj u hu
  simpa only [map_sub, map_mul, map_pow, eval_C, pow_two] using
    quadratic_discriminant_point_bound hδ hU hval hder hcurv

end Submission.Obl.k4_clean_cover_graph_atlas
