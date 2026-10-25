-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceVelCaps

/-!
# Inputs of `EH2` for a source stage that do not depend on the caps

For `eh2_of_ceilings` (x0812): the model coefficients are measurable, the parent test is
quadratic, and the parent's hidden derivative is at least `κ⁻¹` almost everywhere under the
model incidence law, with the path slack `κ` itself (not the model loss `K`), so that the cap
factor `16 (1 + κ²)` is a subpower.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4XInterface

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W}

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The parent test of the stage is quadratic. -/
theorem stage_P_degree (D : SourceData p) (unit : ℝ) :
    (D.stage Nk L unit ν B).P.totalDegree ≤ 2 :=
  ((D.frame Nk B).totalDegree_normTest_le _ _).trans (hp.chart D.parent).2.2.2.2.1

omit hp in
/-- The model coefficients are measurable. -/
theorem stage_b_measurable (D : SourceData p) (unit : ℝ) :
    Measurable (D.stage Nk L unit ν B).b :=
  (D.frame Nk B).measurable_eb

/-- **The parent derivative floor of the model, with the path slack.** -/
theorem stage_parent_deriv_floor (D : SourceData p) (unit : ℝ) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hSm : MeasurableSet D.S)
    (hScount : D.S ⊆ p.counted D.parent) :
    ∀ᵐ z ∂(D.stage Nk L unit ν B).μ,
      p.κ⁻¹ ≤ |eval (exS (D.stage Nk L unit ν B).b z.1 z.2)
        (pderiv (3 : Fin 4) (D.stage Nk L unit ν B).P)| := by
  have hc := hp.chart D.parent
  have hκ := hp.one_le_slack
  have hδ : 0 < δ Nk (p.r D.i₀) := by
    show 0 < (2 : ℝ) ^ (-(⌊p.r D.i₀ * Real.log Nk / Real.log 2⌋ : ℤ))
    positivity
  have hD : IsUnit (D.frame Nk B).F.D.det := by
    rw [D.frame_F]
    show IsUnit D.D₀.det
    rw [hD₀]
    exact isUnit_iff_ne_zero.mpr (MajorFrame.det_ne_zero hc.1)
  have hq0 : (D.frame Nk B).F.q ≠ 0 := by rw [D.frame_F]; exact D.q₀_pos.ne'
  have hsc : (D.frame Nk B).sc = B D.w₀ / δ Nk (p.r D.i₀) := rfl
  have hsc0 : (D.frame Nk B).sc ≠ 0 := by rw [hsc]; positivity
  have hμ : (D.stage Nk L unit ν B).μ = muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S :=
    rfl
  have hb : (D.stage Nk L unit ν B).b = (D.frame Nk B).eb := rfl
  have hP : (D.stage Nk L unit ν B).P =
      (D.frame Nk B).normTest (δ Nk (p.r D.i₀)) (p.test D.parent) := rfl
  have ht₀ : (D.frame Nk B).F.t₀ = D.t₀ := by rw [D.frame_F]
  have hq : (D.frame Nk B).F.q = D.q₀ := by rw [D.frame_F]
  rw [hμ, hb, hP]
  refine ae_muE_of_forall _ _ _ _ D.q₀_pos.ne' hSm fun z hz => ?_
  have hτ : D.t₀ + D.q₀ * ((z.2 - D.t₀) / D.q₀) = z.2 := by
    have := D.q₀_pos.ne'
    field_simp
    ring
  simp only [tnorm]
  rw [(D.frame Nk B).pderiv_normTest, smul_eval, (D.frame Nk B).eval_normTest_at hq0 hD hsc0,
    ht₀, hq, hτ, hsc]
  have hl := (hp.counted_support D.parent z (hScount hz)).2.2.2
  have : (B D.w₀ / δ Nk (p.r D.i₀))⁻¹ * ((δ Nk (p.r D.i₀))⁻¹ *
      eval (gx z.1 z.2) (pderiv 3 (p.test D.parent))) =
      eval (gx z.1 z.2) (pderiv 3 (p.test D.parent)) / B D.w₀ := by field_simp
  rw [this, abs_div, abs_of_pos hBw, le_div_iff₀ hBw]
  calc p.κ⁻¹ * B D.w₀ = B D.w₀ / p.κ := by ring
    _ ≤ _ := hl

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
