import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.QuadraticCellCaps
import Submission.Lib.K4QuadraticSheetCore

/-!
# Fine normalized cells of a regular quadratic candidate

Freezing the base coordinates of a regular quadratic test at a corner of one fine normalized cell
costs a small Lipschitz error, controlled by the coefficient norm. The original bin ceilings for
the scaled residual then bound the mass of the cell (`fine_cell_cap`).
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg)

theorem sum_update_sub_le (z x : Fin 4 → ℝ) (h : ℝ)
    (hz : ∀ i : Fin 3, |x i.castSucc - z i.castSucc| ≤ h) :
    ∑ i, |Function.update z 3 (x 3) i - x i| ≤ 3 * h := by
  have h0 : |x 0 - z 0| ≤ h := hz 0
  have h1 : |x 1 - z 1| ≤ h := hz 1
  have h2 : |x 2 - z 2| ≤ h := hz 2
  rw [Fin.sum_univ_four]
  have e0 : Function.update z 3 (x 3) 0 = z 0 := by simp [Function.update_apply]
  have e1 : Function.update z 3 (x 3) 1 = z 1 := by simp [Function.update_apply]
  have e2 : Function.update z 3 (x 3) 2 = z 2 := by simp [Function.update_apply]
  have e3 : Function.update z 3 (x 3) 3 = x 3 := by simp
  rw [e0, e1, e2, e3, sub_self, abs_zero, abs_sub_comm (z 0), abs_sub_comm (z 1),
    abs_sub_comm (z 2)]
  linarith

/-- **Fine cell cap.** -/
theorem fine_cell_cap {Ω : Type*} [MeasurableSpace Ω] (τ : Measure Ω) (E T : Set Ω)
    (hET : E ⊆ T) (x : Ω → Fin 4 → ℝ) (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (z : Fin 4 → ℝ) {H c h M : ℝ} (hH : 1 ≤ H) (hc : 0 < c)
    (hM : coeffL1 Q ≤ M) (hz : ∀ i, |z i| ≤ 1)
    (hx : ∀ p ∈ E, (∀ i, |x p i| ≤ 1) ∧ (∀ i : Fin 3, |x p i.castSucc - z i.castSucc| ≤ h) ∧
      |eval (x p) Q| ≤ H * c ∧ H⁻¹ ≤ |eval (x p) (pderiv 3 Q)|)
    (hsmall : 2 * M * (3 * h) ≤ H * c) (hsmall' : 2 * (2 * M) * (3 * h) ≤ H⁻¹ / 2)
    (cap : ENNReal) (hcap : ∀ a : ℤ, τ {p | p ∈ T ∧ ⌊x p 3 / c⌋ = a} ≤ cap) :
    τ E ≤ ENNReal.ofReal (8 * (1 + 4 * H ^ 2)) * cap := by
  have hH0 : 0 < H := by linarith
  have hβ : 0 < H⁻¹ := inv_pos.mpr hH0
  have hM0 : 0 ≤ M := (coeffL1_nonneg Q).trans hM
  have key := Transfer.quadratic_candidate_cell_cap τ E T hET x Q hQ z (H := H) (c := c)
    (β := H⁻¹) hH0.le hc hβ ?_ cap hcap
  · have e : 8 * (1 + 4 * H / H⁻¹) = 8 * (1 + 4 * H ^ 2) := by field_simp
    rwa [e] at key
  · refine Filter.Eventually.of_forall (fun p hp => ?_)
    obtain ⟨hxb, hxz, hval, hder⟩ := hx p hp
    have hzx : ∀ i, |Function.update z 3 (x p 3) i| ≤ 1 := by
      intro i
      by_cases hi : i = 3
      · subst hi; simpa using hxb 3
      · simpa [Function.update_apply, hi] using hz i
    have hsum := sum_update_sub_le z (x p) h hxz
    have hsum0 : 0 ≤ ∑ i, |Function.update z 3 (x p 3) i - x p i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hh0 : 0 ≤ h := by
      have := hxz 0
      exact (abs_nonneg _).trans this
    refine ⟨hval, hder, ?_, ?_⟩
    · have hl := Submission.Lib.K4QuadraticSheetCore.abs_eval_sub_eval_le Q _ _ hzx hxb
      have hdeg : (Q.totalDegree : ℝ) ≤ 2 := by exact_mod_cast hQ
      calc _ ≤ Q.totalDegree * coeffL1 Q * ∑ i, |Function.update z 3 (x p 3) i - x p i| := hl
        _ ≤ 2 * M * (3 * h) := by
          have := coeffL1_nonneg Q
          gcongr
        _ ≤ H * c := hsmall
    · have hl := Submission.Lib.K4QuadraticSheetCore.abs_eval_sub_eval_le (pderiv 3 Q) _ _ hzx hxb
      have hdeg : ((pderiv 3 Q).totalDegree : ℝ) ≤ 2 := by
        have := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred Q 3
        have h2 : (pderiv 3 Q).totalDegree ≤ 2 := by omega
        exact_mod_cast h2
      have hcd : coeffL1 (pderiv 3 Q) ≤ 2 * M := by
        have := Submission.Lib.K4QuadraticSheetCore.coeffL1_pderiv_le Q 3
        have hdq : (Q.totalDegree : ℝ) ≤ 2 := by exact_mod_cast hQ
        have := coeffL1_nonneg Q
        nlinarith
      calc _ ≤ (pderiv 3 Q).totalDegree * coeffL1 (pderiv 3 Q) *
            ∑ i, |Function.update z 3 (x p 3) i - x p i| := hl
        _ ≤ 2 * (2 * M) * (3 * h) := by
          have := coeffL1_nonneg (pderiv 3 Q)
          gcongr
        _ ≤ H⁻¹ / 2 := hsmall'

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
