-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceDensityMasks
import Submission.Obl.k4_finite_affine_parent_sources.SourceEH2Inputs
import Submission.Obl.k4_finite_affine_parent_sources.SourceLabelGroups

/-!
# Pure caps of a source stage

For a source stage whose prepared set lies in the original density mask at a fixed depth grid,
every `EH2` cell (base cube of side `N^(-r)`, either observable at width `N^(-s)`) has mass at
most `κ (4 N^h + 2) N^(τ + 2 δ₀ L) (N^(uL))^(-d s) · N^(-3r) · 16 (1 + κ²)`, as soon as the
composed depth `r₀ + u L s` lies within one grid mesh `h` below a grid depth. The derivative
floor is the parent's path slack `κ` (x0891's `stage_parent_deriv_floor`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial Submission.Lib.K4XInterface

noncomputable section

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

theorem stage_N_rpow (Nk L unit s : ℝ) (hNk : 0 < Nk) :
    (Nk ^ (unit * L)) ^ (-s) = Nk ^ (-(unit * L * s)) := by
  rw [← Real.rpow_mul hNk.le]
  ring_nf

/-- **Pure cells of a source stage.** -/
theorem source_pure_cell (D : SourceData p) (unit : ℝ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hNk : 1 < Nk) (hBw : 0 < B D.w₀)
    (hD₀ : D.D₀ = MajorFrame.frame (p.frame D.parent)) (hSm : MeasurableSet D.S)
    (hScount : D.S ⊆ p.counted D.parent)
    {G' : ℕ} {g : ℝ → EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal} {r : Fin G' → ℝ}
    (hg : ∀ j, Measurable (g (r j)))
    (hlaw : ∀ j, (((ν D.w₀).prod volume).restrict (E D.w₀)).map
      (obs (B D.w₀) (δ Nk (r j))) = (volume.prod Measure.count).withDensity (g (r j)))
    {τd h d : ℝ} (hS : D.S ⊆ E D.w₀ ∩ densMask g (B D.w₀) Nk τd f r)
    (hd : 0 ≤ d) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s)
    (j : Fin G') (hj1 : p.r D.i₀ + unit * L * s ≤ r j)
    (hj2 : r j ≤ p.r D.i₀ + unit * L * s + h)
    (hprof : f (p.r D.i₀) + d * (r j - p.r D.i₀) - 2 * (δ₀ * L) ≤ f (r j))
    (rr : ℝ) (hb : Bool) (q : Fin 3 → ℤ) (a : ℤ) :
    (D.stage Nk L unit ν B).μ {z | zS (D.stage Nk L unit ν B).b (D.stage Nk L unit ν B).N rr z = q ∧
        ⌊(if hb then eval (exS (D.stage Nk L unit ν B).b z.1 z.2) (D.stage Nk L unit ν B).P
          else (exS (D.stage Nk L unit ν B).b z.1 z.2) 3) /
          ((D.stage Nk L unit ν B).N ^ (-s))⌋ = a} ≤
      ENNReal.ofReal (p.κ * (4 * Nk ^ h + 2) * Nk ^ (τd + 2 * (δ₀ * L)) *
          Nk ^ (-(d * (unit * L * s)))) *
        (ENNReal.ofReal (((D.stage Nk L unit ν B).N ^ (-rr)) ^ 3) *
          ENNReal.ofReal (16 * (1 + p.κ ^ 2))) := by
  have hNk0 : 0 < Nk := by linarith
  letI : IsProbabilityMeasure (ν D.w₀) := hν D.w₀
  have hq : 0 < (D.frame Nk B).F.q := by rw [D.frame_F]; exact D.q₀_pos
  have hD : IsUnit (D.frame Nk B).F.D.det := by
    rw [D.frame_F]
    show IsUnit D.D₀.det
    rw [hD₀]
    exact isUnit_iff_ne_zero.mpr (MajorFrame.det_ne_zero (hp.chart D.parent).1)
  have hdetQ : 0 < |(p.frame D.parent).det| := abs_pos.mpr (hp.chart D.parent).1
  have hdet : |(D.frame Nk B).F.D.det| ≤ |(p.frame D.parent).det| := by
    rw [D.frame_F]
    show |D.D₀.det| ≤ _
    rw [hD₀]
    exact (MajorFrame.abs_det (hp.chart D.parent).1).le
  have hfloor := label_prior_floor hp hNk0 D.parent
  have hA₀t : ν D.w₀ (p.assigned D.parent) ≠ ⊤ := measure_ne_top _ _
  have hceil := pframe_pure_ceiling (D.frame Nk B) hq hD hNk rfl hp.one_le_slack hdetQ hdet
    (ν D.w₀) (p.assigned D.parent) hA₀t hfloor hg hlaw hS hd hs hh j hj1 hj2 hprof
  have hN : (D.stage Nk L unit ν B).N ^ (-s) = Nk ^ (-(unit * L * s)) :=
    stage_N_rpow hp Nk L unit s hNk0
  have hμ : (D.stage Nk L unit ν B).μ =
      muE (ν D.w₀) (p.assigned D.parent) (D.frame Nk B).F.t₀ (D.frame Nk B).F.q D.S := by
    rw [D.frame_F]; rfl
  have hbeq : (D.stage Nk L unit ν B).b = (D.frame Nk B).eb := rfl
  have hεpos : 0 < (D.stage Nk L unit ν B).N ^ (-rr) := by
    show 0 < (Nk ^ (unit * L)) ^ (-rr)
    positivity
  have hcap' : (D.stage Nk L unit ν B).μ.map
      (obsS (D.stage Nk L unit ν B).b ((D.stage Nk L unit ν B).N ^ (-s))) ≤
      ENNReal.ofReal (p.κ * (4 * Nk ^ h + 2) * Nk ^ (τd + 2 * (δ₀ * L)) *
        Nk ^ (-(d * (unit * L * s)))) • (volume.prod Measure.count) := by
    rw [hμ, hbeq, hN]
    exact hceil
  have hder := SourceData.stage_parent_deriv_floor hp D unit hBw hD₀ hSm hScount
  exact cell_cap_of_ceiling _ (SourceData.stage_b_measurable D unit) _
    (SourceData.stage_P_degree hp D unit)
    hp.one_le_slack hder (by rw [hN]; positivity) _ hcap' hεpos hb q a

end

end

end Submission.Obl.k4_finite_affine_parent_sources
