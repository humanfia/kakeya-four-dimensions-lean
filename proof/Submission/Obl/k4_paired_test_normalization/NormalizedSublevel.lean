-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/NormalizedSublevel.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.CoefficientAnchor
import Submission.Obl.k4_paired_test_normalization.Normalization
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Anchor

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial Set Metric MeasureTheory

/-- One real anchor controls the coefficient l1 size, uniformly at fixed degree. -/
theorem coefficient_size_anchor (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
      ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ (1 : ℝ) / 8 ∧
        coefficientSize P ≤ C * |eval (fun i => z i) P| := by
  classical
  obtain ⟨K, hK, hanchor⟩ := polynomial_coefficient_anchor D (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨((monomialSet 3 D).card : ℝ) * K + 1, by positivity, ?_⟩
  intro P hP
  obtain ⟨z, hz, hc⟩ := hanchor P hP
  refine ⟨z, hz, ?_⟩
  have hcard : (P.support.card : ℝ) ≤ (monomialSet 3 D).card := by
    exact_mod_cast Finset.card_le_card (support_subset_monomialSet P hP)
  calc
    coefficientSize P ≤ ∑ _m ∈ P.support, K * |eval (fun i => z i) P| :=
      Finset.sum_le_sum (fun m _ => hc m)
    _ = (P.support.card : ℝ) * (K * |eval (fun i => z i) P|) := by simp
    _ ≤ ((monomialSet 3 D).card : ℝ) * (K * |eval (fun i => z i) P|) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (((monomialSet 3 D).card : ℝ) * K + 1) * |eval (fun i => z i) P| := by
      nlinarith [abs_nonneg (eval (fun i => z i) P)]

/-- Coefficient size supplies the real anchor for the accepted radial sublevel bound. -/
theorem coefficient_size_sublevel :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ 2 →
      ∀ ρ η θ : ℝ, ρ ≤ coefficientSize P → 0 < θ → θ ≤ 1 → 0 ≤ η →
        576 * C * η < ρ * θ ^ 2 →
        volume {x : EuclideanSpace ℝ (Fin 3) | x ∈ closedBall 0 (1 / 8) ∧
          |eval (fun i => x i) P| ≤ η} ≤
        ENNReal.ofReal (128 * θ) * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8)) := by
  obtain ⟨C, hC, hanchor⟩ := coefficient_size_anchor 2
  refine ⟨C, hC, ?_⟩
  intro P hP ρ η θ hρ hθ hθ1 hη hsmall
  obtain ⟨z, hz, hsize⟩ := hanchor P hP
  have hm : ρ / C ≤ |eval (fun i => z i) P| := (div_le_iff₀ hC).mpr (by nlinarith)
  have hsmall' : 576 * η < (ρ / C) * θ ^ 2 := by
    calc
      576 * η < (ρ * θ ^ 2) / C := (lt_div_iff₀ hC).mpr (by nlinarith)
      _ = (ρ / C) * θ ^ 2 := by ring
  exact Submission.Obl.k4_quadratic_discriminant_safe_paths.volume_anchor_sublevel_le
    P hP z hz hθ hθ1 hη hm hsmall'

/-- Normalize every equation first. Small normalized discriminants occupy a
uniformly small real volume whenever the original discriminant has a real anchor. -/
theorem normalized_discriminant_sublevel :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MvPolynomial (Fin 4) ℝ, (disc P).totalDegree ≤ 2 →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ coefficientSize (disc P) →
        ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ (∀ m, |(disc (MvPolynomial.C t * P)).coeff m| ≤ 1) ∧
          ∀ η θ : ℝ, 0 < θ → θ ≤ 1 → 0 ≤ η →
            1152 * C * η < min ρ 1 * θ ^ 2 →
            volume {x : EuclideanSpace ℝ (Fin 3) | x ∈ closedBall 0 (1 / 8) ∧
              |eval (fun i => x i) (disc (MvPolynomial.C t * P))| ≤ η} ≤
            ENNReal.ofReal (128 * θ) *
              volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8)) := by
  obtain ⟨C, hC, hsublevel⟩ := coefficient_size_sublevel
  refine ⟨C, hC, ?_⟩
  intro P hP ρ hρ hρsize
  obtain ⟨t, ht, ht1, hc, hsize⟩ := exists_discriminant_normalization P
  refine ⟨t, ht, ht1, hc, ?_⟩
  intro η θ hθ hθ1 hη hsmall
  have hdegree : (disc (MvPolynomial.C t * P)).totalDegree ≤ 2 := by
    rw [disc_C_mul]
    have hmul := MvPolynomial.totalDegree_mul
      (MvPolynomial.C (t ^ 2) : MvPolynomial (Fin 3) ℝ) (disc P)
    rw [MvPolynomial.totalDegree_C, zero_add] at hmul
    exact hmul.trans hP
  apply hsublevel (disc (MvPolynomial.C t * P)) hdegree (min ρ 1 / 2) η θ ?_ hθ hθ1 hη ?_
  · exact (div_le_div_of_nonneg_right (min_le_min_right 1 hρsize) (by norm_num)).trans hsize
  · nlinarith

end Submission.Obl.k4_paired_test_normalization
