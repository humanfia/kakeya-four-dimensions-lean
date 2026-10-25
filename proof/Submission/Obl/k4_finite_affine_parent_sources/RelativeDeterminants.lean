-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.Path
import Submission.Obl.k4_finite_affine_parent_sources.MajorFrame
import Submission.Obl.k4_finite_affine_parent_sources.VelocityFrame

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Submission.Lib.K4XInterface

noncomputable section

/-- Both sides of the actual normalized determinant ratio follow from
the original cumulative narrowness bounds and the unchanged major frame. -/
theorem PathData.Valid.relative_major_determinant_bounds
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (parent child : Fin p.C) :
    let M := relativeVelocityFrame (((2 : ℝ) ^ p.T (p.lev parent))⁻¹)
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹)
      (MajorFrame.frame (p.frame parent)) (p.frame child)
    Nk ^ (-(p.nw (p.lev child) - p.nw (p.lev parent) + 2 * (δ₀ * L))) ≤ |M.det| ∧
      |M.det| ≤ Nk ^ (-(p.nw (p.lev child) - p.nw (p.lev parent) - 2 * (δ₀ * L))) := by
  dsimp only
  have hparent := hp.narrowness parent
  have hchild := hp.narrowness child
  have hQ := (hp.chart parent).1
  have hD := MajorFrame.det_ne_zero hQ
  have hdet := MajorFrame.abs_det hQ
  have hp0 : Nk ^ (-(p.nw (p.lev parent) + δ₀ * L)) ≤
      |(MajorFrame.frame (p.frame parent)).det| * (4 : ℝ) ^ p.T (p.lev parent) := by
    simpa only [hdet] using hparent.1
  have hp1 : |(MajorFrame.frame (p.frame parent)).det| * (4 : ℝ) ^ p.T (p.lev parent) ≤
      Nk ^ (-(p.nw (p.lev parent) - δ₀ * L)) := by
    simpa only [hdet] using hparent.2
  exact ⟨relativeVelocityFrame_narrowness_lower hNk hD hp1 hchild.1,
    relativeVelocityFrame_narrowness_bound hNk hp0 hchild.2⟩

/-- Profile rounding produces one explicit common multiplicative loss
for the two determinant bounds. The exponent is measured in original
units and can be absorbed in the final native geometric slack. -/
theorem PathData.Valid.relative_profile_determinant_bounds
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sgrid : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sgrid δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (parent child : Fin p.C) (u s error : ℝ)
    (hprofile : |p.nw (p.lev child) - p.nw (p.lev parent) - ℓ * u * s| ≤ error) :
    let M := relativeVelocityFrame (((2 : ℝ) ^ p.T (p.lev parent))⁻¹)
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹)
      (MajorFrame.frame (p.frame parent)) (p.frame child)
    Nk ^ (-ℓ * u * s) / Nk ^ (error + 2 * (δ₀ * L)) ≤ |M.det| ∧
      |M.det| ≤ Nk ^ (error + 2 * (δ₀ * L)) * Nk ^ (-ℓ * u * s) := by
  dsimp only
  have hN : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have hdet := hp.relative_major_determinant_bounds hN parent child
  have habs := abs_le.mp hprofile
  constructor
  · calc
      _ = Nk ^ (-ℓ * u * s - (error + 2 * (δ₀ * L))) := by
        rw [Real.rpow_sub hN]
      _ ≤ Nk ^ (-(p.nw (p.lev child) - p.nw (p.lev parent) + 2 * (δ₀ * L))) :=
        Real.rpow_le_rpow_of_exponent_le hNk (by linarith)
      _ ≤ _ := hdet.1
  · calc
      _ ≤ Nk ^ (-(p.nw (p.lev child) - p.nw (p.lev parent) - 2 * (δ₀ * L))) := hdet.2
      _ ≤ Nk ^ (error + 2 * (δ₀ * L) + (-ℓ * u * s)) :=
        Real.rpow_le_rpow_of_exponent_le hNk (by linarith)
      _ = _ := Real.rpow_add hN _ _

/-- The same two bounds in the native resolution, with one common slack.
This is the determinant certificate consumed by the label geometry and
the original-candidate return statement. -/
theorem PathData.Valid.relative_native_determinant_bounds
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sgrid : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sgrid δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (parent child : Fin p.C) (u s error H : ℝ)
    (hprofile : |p.nw (p.lev child) - p.nw (p.lev parent) - ℓ * u * s| ≤ error)
    (hH : Nk ^ (error + 2 * (δ₀ * L)) ≤ H) :
    let M := relativeVelocityFrame (((2 : ℝ) ^ p.T (p.lev parent))⁻¹)
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹)
      (MajorFrame.frame (p.frame parent)) (p.frame child)
    (Nk ^ u) ^ (-ℓ * s) / H ≤ |M.det| ∧
      |M.det| ≤ H * (Nk ^ u) ^ (-ℓ * s) := by
  dsimp only
  have hN : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have he : 0 < Nk ^ (error + 2 * (δ₀ * L)) := Real.rpow_pos_of_pos hN _
  have hg : (Nk ^ u) ^ (-ℓ * s) = Nk ^ (-ℓ * u * s) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [hg]
  have hb := hp.relative_profile_determinant_bounds hNk parent child u s error hprofile
  refine ⟨?_, hb.2.trans ?_⟩
  · exact (div_le_div_of_nonneg_left (by positivity) he hH).trans hb.1
  · exact mul_le_mul_of_nonneg_right hH (by positivity)

end

end Submission.Obl.k4_finite_affine_parent_sources
