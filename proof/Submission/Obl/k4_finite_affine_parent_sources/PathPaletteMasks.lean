-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PaletteMasks

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4AngularCharge
open scoped ENNReal

noncomputable section

/-- Impose the original conditional-share floor at every eligible
parent level, before the information window chooses its parent. -/
def PathData.parentShareMask {W : ℕ} (p : PathData W)
    (μ : Fin W → Measure Incidence) [∀ w, IsFiniteMeasure (μ w)]
    (Nk L : ℝ) (B : Fin W → ℝ) (levels : Finset ℕ) (θ : ℝ≥0∞) (w : Fin W) :
    Set Incidence :=
  ⋂ i : levels, PaletteMasks.shares (μ w) (obs (B w) (δ Nk L))
    (fun b : {b : Fin p.C // p.lev b = i.val ∧ p.world b = w} => p.counted b.val) θ

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

theorem PathData.Valid.measurableSet_parentShareMask
    (μ : Fin W → Measure Incidence) [∀ w, IsFiniteMeasure (μ w)]
    (levels : Finset ℕ) (θ : ℝ≥0∞) (w : Fin W) :
    MeasurableSet (p.parentShareMask μ Nk L B levels θ w) := by
  apply MeasurableSet.iInter
  intro i
  exact PaletteMasks.measurableSet_shares (μ w) (obs (B w) (δ Nk L))
    (Submission.Lib.K4ExactProblemOps.measurable_obs _ _)
    (fun b : {b : Fin p.C // p.lev b = i.val ∧ p.world b = w} => p.counted b.val)
    (fun b => hp.counted_measurable b.val) θ

theorem PathData.Valid.parentShareMask_loss
    (μ : Fin W → Measure Incidence) [∀ w, IsFiniteMeasure (μ w)]
    (hNk : 1 ≤ Nk) (levels : Finset ℕ)
    (hdepths : ∀ i ∈ levels, 0 ≤ p.r i ∧ p.r i ≤ L)
    (Kc : ℕ) (hKc : p.κ ≤ Kc) (θ : ℝ≥0∞) (w : Fin W) :
    μ w (p.parentShareMask μ Nk L B levels θ w)ᶜ ≤
      levels.card * Kc * θ * μ w univ := by
  classical
  rw [PathData.parentShareMask, compl_iInter]
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    _ ≤ ∑ _i : levels, (Kc : ℝ≥0∞) * θ * μ w univ := by
      apply Finset.sum_le_sum
      intro i _
      exact hp.level_share_loss (μ w) hNk i.val (hdepths i.val i.property).1
        (hdepths i.val i.property).2 w Kc hKc θ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring

theorem PathData.Valid.parentShareMask_weighted_loss
    (μ : Fin W → Measure Incidence) [∀ w, IsFiniteMeasure (μ w)]
    (hNk : 1 ≤ Nk) (levels : Finset ℕ)
    (hdepths : ∀ i ∈ levels, 0 ≤ p.r i ∧ p.r i ≤ L)
    (Kc : ℕ) (hKc : p.κ ≤ Kc) (θ : ℝ≥0∞) :
    (∑ w, ENNReal.ofReal (ω w) * μ w (p.parentShareMask μ Nk L B levels θ w)ᶜ) ≤
      (levels.card * Kc * θ) * ∑ w, ENNReal.ofReal (ω w) * μ w univ := by
  calc
    _ ≤ ∑ w, ENNReal.ofReal (ω w) * (levels.card * Kc * θ * μ w univ) :=
      Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl
        (hp.parentShareMask_loss μ hNk levels hdepths Kc hKc θ w)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring

end Path

end
end Submission.Obl.k4_finite_affine_parent_sources
