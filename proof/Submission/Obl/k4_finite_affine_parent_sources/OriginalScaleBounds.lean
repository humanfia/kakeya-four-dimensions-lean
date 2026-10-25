-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.RelativeDeterminants

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Submission.Lib.K4XInterface

noncomputable section

/-- Two original profile errors and one fixed-grid rounding error give
the relative profile error. -/
theorem two_point_affine_grid_error
    (a b sp sc target d L error gap : ℝ) (hd : 0 ≤ d) (hL : 0 ≤ L)
    (ha : |a - d * sp * L| ≤ error * L)
    (hb : |b - d * sc * L| ≤ error * L)
    (hgrid : |sc - sp - target| ≤ gap) :
    |b - a - d * target * L| ≤ (2 * error + d * gap) * L := by
  calc
    _ = |(b - d * sc * L) - (a - d * sp * L) + d * L * (sc - sp - target)| := by
      congr 1
      ring
    _ ≤ |(b - d * sc * L) - (a - d * sp * L)| + |d * L * (sc - sp - target)| :=
      abs_add_le _ _
    _ ≤ (|b - d * sc * L| + |a - d * sp * L|) +
        (d * L) * |sc - sp - target| := by
      exact add_le_add (abs_sub _ _)
        (by rw [abs_mul, abs_of_nonneg (mul_nonneg hd hL)])
    _ ≤ (error * L + error * L) + (d * L) * gap :=
      add_le_add (add_le_add hb ha) (mul_le_mul_of_nonneg_left hgrid (mul_nonneg hd hL))
    _ = _ := by ring

/-- Fixed grid rounding controls both actual depth and actual cumulative
narrowness. The two error bounds retain their distinct coefficients. -/
theorem PathData.Valid.relative_grid_offsets
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)
    (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L) (parent child : Fin p.C) (unit s gap : ℝ)
    (hgrid : |sg (p.lev child) - sg (p.lev parent) - unit * s| ≤ gap) :
    |p.r (p.lev child) - p.r (p.lev parent) - unit * L * s| ≤ (2 * δ₀ + gap) * L ∧
      |p.nw (p.lev child) - p.nw (p.lev parent) - ℓ * (unit * L) * s| ≤
        (2 * δ₀ + ℓ * gap) * L := by
  have hp0 := hp.level_bounds _ (hp.label_level parent)
  have hp1 := hp.level_bounds _ (hp.label_level child)
  constructor
  · have hh := two_point_affine_grid_error (p.r (p.lev parent)) (p.r (p.lev child))
      (sg (p.lev parent)) (sg (p.lev child)) (unit * s) 1 L δ₀ gap (by norm_num) hL
      (by simpa only [one_mul] using hp0.1) (by simpa only [one_mul] using hp1.1) hgrid
    convert hh using 1 <;> congr 1 <;> ring
  · have hh := two_point_affine_grid_error (p.nw (p.lev parent)) (p.nw (p.lev child))
      (sg (p.lev parent)) (sg (p.lev child)) (unit * s) ℓ L δ₀ gap hℓ hL
      hp0.2.2.2.2.1 hp1.2.2.2.2.1 hgrid
    convert hh using 1 <;> congr 1 <;> ring

/-- The native determinant bounds now consume the original fixed-grid
rounding estimate, with its exact cumulative error exponent. -/
theorem PathData.Valid.relative_native_determinant_of_grid
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L)
    (parent child : Fin p.C) (unit s gap H : ℝ)
    (hgrid : |sg (p.lev child) - sg (p.lev parent) - unit * s| ≤ gap)
    (hH : Nk ^ ((4 * δ₀ + ℓ * gap) * L) ≤ H) :
    let M := relativeVelocityFrame (((2 : ℝ) ^ p.T (p.lev parent))⁻¹)
      (((2 : ℝ) ^ p.T (p.lev child))⁻¹)
      (MajorFrame.frame (p.frame parent)) (p.frame child)
    (Nk ^ (unit * L)) ^ (-ℓ * s) / H ≤ |M.det| ∧
      |M.det| ≤ H * (Nk ^ (unit * L)) ^ (-ℓ * s) := by
  have hprofile := (hp.relative_grid_offsets hℓ hL parent child unit s gap hgrid).2
  apply hp.relative_native_determinant_bounds hNk parent child (unit * L) s
    ((2 * δ₀ + ℓ * gap) * L) H hprofile
  convert hH using 1
  congr 1
  ring

/-- The same fixed-grid rounding gives the true native dyadic time
exponent, with two original time errors and one rounded depth gap. -/
theorem PathData.Valid.relative_native_time_of_grid
    {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)
    (hNk : 1 ≤ Nk) (hκ : 0 ≤ κ₁) (hL : 0 ≤ L)
    (parent child : Fin p.C) (unit s gap : ℝ)
    (hgrid : |sg (p.lev child) - sg (p.lev parent) - unit * s| ≤ gap)
    (hT : p.T (p.lev parent) ≤ p.T (p.lev child)) :
    (Nk ^ (unit * L)) ^ (κ₁ * s) / Nk ^ ((2 * δ₀ + κ₁ * gap) * L) ≤
        (2 : ℝ) ^ (p.T (p.lev child) - p.T (p.lev parent)) ∧
      (2 : ℝ) ^ (p.T (p.lev child) - p.T (p.lev parent)) ≤
        Nk ^ ((2 * δ₀ + κ₁ * gap) * L) * (Nk ^ (unit * L)) ^ (κ₁ * s) := by
  have hN : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have hnative : (Nk ^ (unit * L)) ^ (κ₁ * s) = Nk ^ ((unit * L) * (κ₁ * s)) :=
    (Real.rpow_mul hN.le _ _).symm
  have hp0 := hp.level_bounds _ (hp.label_level parent)
  have hp1 := hp.level_bounds _ (hp.label_level child)
  have hpow : (2 : ℝ) ^ p.T (p.lev child) =
      (2 : ℝ) ^ p.T (p.lev parent) *
        (2 : ℝ) ^ (p.T (p.lev child) - p.T (p.lev parent)) := by
    rw [← pow_add, Nat.add_sub_of_le hT]
  have hratio : (2 : ℝ) ^ (p.T (p.lev child) - p.T (p.lev parent)) =
      (2 : ℝ) ^ p.T (p.lev child) / (2 : ℝ) ^ p.T (p.lev parent) := by
    rw [hpow]
    field_simp <;> ring
  have hmul : |κ₁ * L * (sg (p.lev child) - sg (p.lev parent) - unit * s)| ≤
      κ₁ * L * gap := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hκ hL)]
    exact mul_le_mul_of_nonneg_left hgrid (mul_nonneg hκ hL)
  have habs := abs_le.mp hmul
  rw [hratio]
  constructor
  · calc
      _ = Nk ^ ((unit * L) * (κ₁ * s) - (2 * δ₀ + κ₁ * gap) * L) := by
        rw [hnative, Real.rpow_sub hN]
      _ ≤ Nk ^ ((κ₁ * sg (p.lev child) - δ₀) * L -
          (κ₁ * sg (p.lev parent) + δ₀) * L) :=
        Real.rpow_le_rpow_of_exponent_le hNk (by nlinarith only [habs.1])
      _ = Nk ^ ((κ₁ * sg (p.lev child) - δ₀) * L) /
          Nk ^ ((κ₁ * sg (p.lev parent) + δ₀) * L) := Real.rpow_sub hN _ _
      _ ≤ _ := div_le_div₀ (by positivity) hp1.2.2.1 (by positivity) hp0.2.2.2.1
  · calc
      _ ≤ Nk ^ ((κ₁ * sg (p.lev child) + δ₀) * L) /
          Nk ^ ((κ₁ * sg (p.lev parent) - δ₀) * L) :=
        div_le_div₀ (by positivity) hp1.2.2.2.1 (by positivity) hp0.2.2.1
      _ = Nk ^ ((κ₁ * sg (p.lev child) + δ₀) * L -
          (κ₁ * sg (p.lev parent) - δ₀) * L) := (Real.rpow_sub hN _ _).symm
      _ ≤ Nk ^ ((2 * δ₀ + κ₁ * gap) * L + (unit * L) * (κ₁ * s)) :=
        Real.rpow_le_rpow_of_exponent_le hNk (by nlinarith only [habs.2])
      _ = _ := by rw [Real.rpow_add hN, hnative]

end

end Submission.Obl.k4_finite_affine_parent_sources
