/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/StableGrid.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.PolynomialLipschitz
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SheetBridge

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open Set Metric MvPolynomial

/-- A positive real discriminant remains in the right half plane on a nearby
complex grid ball. The constant is independent of the equation's coefficients. -/
theorem exists_disc_grid_lower_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ),
      (disc P).totalDegree ≤ 2 → ∀ A F r : ℝ, 0 ≤ A → 0 < F → 0 < r →
      r ≤ 1 / 16 → (∀ d, |(disc P).coeff d| ≤ A) →
      ∀ z c : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 8 → ‖z - c‖ ≤ r →
        F ≤ eval (fun i => z i) (disc P) →
          ∀ ζ ∈ ball (emb c) (8 * r),
            F - 9 * C * A * r ≤ (eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ))).re := by
  obtain ⟨C, hC, hLip⟩ :=
    Submission.Obl.k4_paired_sheet_discrepancy_matching.exists_complex_lipschitz_from_coefficients
      3 2 1
  refine ⟨C, hC, ?_⟩
  intro P hdeg A F r hA hF hr hr16 hcoeff z c hz hzc hfloor ζ hζ
  have hdist : ‖ζ - emb z‖ < 9 * r := by
    have hball := mem_ball_iff_norm.mp hζ
    have hemb : ‖emb c - emb z‖ ≤ r := by
      rw [emb_sub, norm_emb, norm_sub_rev]
      exact hzc
    calc ‖ζ - emb z‖ ≤ ‖ζ - emb c‖ + ‖emb c - emb z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 9 * r := by linarith
  have hnormζ : ‖ζ‖ ≤ 1 := by
    have : ‖ζ‖ ≤ ‖ζ - emb z‖ + ‖emb z‖ := norm_le_norm_sub_add _ _
    rw [norm_emb] at this
    linarith
  have hpi (w : EuclideanSpace ℂ (Fin 3)) : ‖(fun i => w i)‖ ≤ ‖w‖ := by
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr (PiLp.norm_apply_le w)
  have hnormz : ‖(fun i => (emb z) i)‖ ≤ 1 := by
    exact (hpi _).trans (by rw [norm_emb]; linarith)
  have hdiffpi : ‖(fun i => ζ i) - (fun i => (emb z) i)‖ ≤ ‖ζ - emb z‖ := by
    exact hpi (ζ - emb z)
  have hdiff :
      ‖eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ)) -
        (eval (fun i => z i) (disc P) : ℂ)‖ ≤ 9 * C * A * r := by
    have heq := eval_complexification (disc P) (fun i => z i)
    change eval (fun i => (emb z) i) ((disc P).map (algebraMap ℝ ℂ)) = _ at heq
    rw [← heq]
    simp only [eval_map]
    calc _ ≤ C * A * ‖(fun i => ζ i) - (fun i => (emb z) i)‖ :=
          hLip (disc P) hdeg A hA hcoeff _ _ ((hpi _).trans hnormζ) hnormz
      _ ≤ C * A * ‖ζ - emb z‖ :=
          mul_le_mul_of_nonneg_left hdiffpi (mul_nonneg hC.le hA)
      _ ≤ C * A * (9 * r) :=
          mul_le_mul_of_nonneg_left hdist.le (mul_nonneg hC.le hA)
      _ = 9 * C * A * r := by ring
  have hre := Complex.abs_re_le_norm
    (eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ)) -
      (eval (fun i => z i) (disc P) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have := neg_abs_le
    ((eval (fun i => ζ i) ((disc P).map (algebraMap ℝ ℂ))).re -
      eval (fun i => z i) (disc P))
  linarith

/-- A positive source floor gives a simple sheet on the complex grid ball. -/
theorem exists_discPosOn_grid_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ),
      (disc P).totalDegree ≤ 2 → ∀ A F r : ℝ, 0 ≤ A → 0 < F → 0 < r →
      r ≤ 1 / 16 → (∀ d, |(disc P).coeff d| ≤ A) →
      ∀ z c : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ 1 / 8 → ‖z - c‖ ≤ r →
        F ≤ eval (fun i => z i) (disc P) → 9 * C * A * r < F →
          DiscPosOn P c r := by
  obtain ⟨C, hC, hspec⟩ := exists_disc_grid_lower_constant
  refine ⟨C, hC, ?_⟩
  intro P hdeg A F r hA hF hr hr16 hcoeff z c hz hzc hfloor hsmall ζ hζ
  have hlower := hspec P hdeg A F r hA hF hr hr16 hcoeff z c hz hzc hfloor ζ hζ
  linarith

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
