-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/QuadraticReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.ParentFrame
import Submission.Obl.k4_finite_affine_candidate_return.Original

namespace Submission.Obl.k4_finite_affine_candidate_return

open MvPolynomial Submission.Lib.K4XInterface

noncomputable section

namespace PFrame

/-- The first derivative returns in the original hidden-derivative unit. -/
theorem eval_pderiv_liftE (Φ : PFrame) (hq : Φ.F.q ≠ 0) (δ B : ℝ)
    (hδ : δ ≠ 0) (hsc : Φ.sc = B / δ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (gx l t) (pderiv (3 : Fin 4) (Φ.liftE δ Q)) =
      B * eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q)) (pderiv (3 : Fin 4) Q) := by
  rw [Φ.pderiv_liftE, smul_eval, Φ.eval_liftE hq, hsc]
  field_simp

/-- The second derivative returns with the square of the derivative unit. -/
theorem eval_pderiv_pderiv_liftE (Φ : PFrame) (hq : Φ.F.q ≠ 0) (δ B : ℝ)
    (hδ : δ ≠ 0) (hsc : Φ.sc = B / δ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (gx l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (Φ.liftE δ Q))) =
      (B ^ 2 / δ) * eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q))
        (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) := by
  rw [Φ.pderiv_liftE, Derivation.map_smul, smul_eval,
    Φ.eval_pderiv_liftE hq δ B hδ hsc, hsc]
  ring

/-- A model fit returns throughout the actual old block, with explicit
allowances for the comparison between tangent and original thicknesses. -/
theorem fitS_return (Φ : PFrame) (hq : Φ.F.q ≠ 0) (δ B a a₀ H C : ℝ)
    (hδ : 0 < δ) (hB : 0 ≤ B) (ha : 0 < a) (ha₀ : 0 < a₀)
    (hsc : Φ.sc = B / δ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (I I' : Set ℝ)
    (hI : ∀ t ∈ I, (t - Φ.F.t₀) / Φ.F.q ∈ I')
    (hfit : fitS Φ.eb H a Q l I')
    (hvalue : δ * (H * a) ≤ C * a₀) (hfirst : H ≤ C)
    (hsecond : H * a₀ ≤ C * δ * a) :
    Fits C a₀ B (Φ.liftE δ Q) l I := by
  intro t ht
  obtain ⟨h0, h1, h2⟩ := hfit _ (hI t ht)
  change |eval (gx l t) (Φ.liftE δ Q)| ≤ C * a₀ ∧
    |eval (gx l t) (pderiv (3 : Fin 4) (Φ.liftE δ Q))| ≤ C * B ∧
    |eval (gx l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (Φ.liftE δ Q)))| ≤ C * B ^ 2 / a₀
  rw [Φ.eval_liftE hq, Φ.eval_pderiv_liftE hq δ B hδ.ne' hsc,
    Φ.eval_pderiv_pderiv_liftE hq δ B hδ.ne' hsc,
    abs_mul, abs_of_pos hδ, abs_mul, abs_of_nonneg hB,
    abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg B) hδ.le)]
  refine ⟨(mul_le_mul_of_nonneg_left h0 hδ.le).trans hvalue,
    (mul_le_mul_of_nonneg_left h1 hB).trans ?_, ?_⟩
  · nlinarith
  · calc
      (B ^ 2 / δ) * |eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q))
          (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))|
        ≤ (B ^ 2 / δ) * (H / a) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (sq_nonneg B) hδ.le)
      _ = (H / (δ * a)) * B ^ 2 := by ring
      _ ≤ (C / a₀) * B ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
        exact (div_le_div_iff₀ (mul_pos hδ ha) ha₀).mpr (by simpa only [mul_assoc] using hsecond)
      _ = C * B ^ 2 / a₀ := by ring

/-- Counted derivative lower bounds retain the original unit as well. -/
theorem lower_return (Φ : PFrame) (hq : Φ.F.q ≠ 0) (δ B H C : ℝ)
    (hδ : δ ≠ 0) (hB : 0 ≤ B) (hH : 0 < H) (hHC : H ≤ C)
    (hsc : Φ.sc = B / δ) (Q : MvPolynomial (Fin 4) ℝ)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ)
    (hlower : H⁻¹ ≤ |eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q)) (pderiv (3 : Fin 4) Q)|) :
    B / C ≤ |eval (gx l t) (pderiv (3 : Fin 4) (Φ.liftE δ Q))| := by
  rw [Φ.eval_pderiv_liftE hq δ B hδ hsc, abs_mul, abs_of_nonneg hB]
  calc B / C ≤ B / H := div_le_div_of_nonneg_left hB hH hHC
    _ = B * H⁻¹ := div_eq_mul_inv _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower hB

end PFrame

end

end Submission.Obl.k4_finite_affine_candidate_return
