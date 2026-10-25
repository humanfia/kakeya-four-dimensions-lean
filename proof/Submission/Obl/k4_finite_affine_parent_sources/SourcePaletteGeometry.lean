-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceTrackingGeometry

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Submission.Lib.K4XInterface
open Submission.Obl.k4_compatible_pair_frame_preparation.Construction

noncomputable section

namespace MajorFrame

theorem minor_column_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (e : Fin 2) :
    |frame Q e 1| ≤ r₂ Q := by
  have hn : |nrm Q e| ≤ 1 := by
    simpa only [Real.norm_eq_abs, norm_nrm hQ] using PiLp.norm_apply_le (nrm Q) e
  have heq : frame Q e 1 = r₂ Q * nrm Q e := by fin_cases e <;> rfl
  rw [heq, abs_mul, abs_of_nonneg (r₂_nonneg Q)]
  exact mul_le_of_le_one_right (r₂_nonneg Q) hn

/-- Fullness turns any normalized area estimate into the physical minor
velocity scale required by the angular palette. -/
theorem minor_ratio_le_of_area (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (q H a : ℝ) (hq : 0 < q) (hH : 0 < H)
    (hfull : q / H ≤ r₁ Q) (harea : |Q.det| ≤ q ^ 2 * a / H) :
    r₂ Q / q ≤ a := by
  have hr : r₂ Q ≤ q * a := by
    dsimp only [r₂]
    calc
      _ ≤ (q ^ 2 * a / H) / (q / H) :=
        div_le_div₀ ((abs_nonneg _).trans harea) harea (by positivity) hfull
      _ = _ := by field_simp <;> ring
  apply (div_le_iff₀ hq).mpr
  simpa only [mul_comm] using hr

theorem normalized_minor_column_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0)
    (q H a : ℝ) (hq : 0 < q) (hH : 0 < H)
    (hfull : q / H ≤ r₁ Q) (harea : |Q.det| ≤ q ^ 2 * a / H) (e : Fin 2) :
    |(q⁻¹ • frame Q) e 1| ≤ a := by
  calc
    _ = |frame Q e 1| / q := by
      simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hq]
      ring
    _ ≤ r₂ Q / q := div_le_div_of_nonneg_right (minor_column_le Q hQ e) hq.le
    _ ≤ a := minor_ratio_le_of_area Q hQ q H a hq hH hfull harea

end MajorFrame

/-- The fixed positive parent band pays all tested palette widths once
the native unit is small compared with `ℓ/(n+2)`. -/
theorem palette_parent_exponent_gap (ℓ unit β sp δ v n : ℝ)
    (hℓ : 0 ≤ ℓ) (hu : 0 ≤ unit) (hβ : β ≤ 1)
    (hband : 1 / 8 ≤ sp) (hunit : unit * (n + 2) ≤ ℓ / 8)
    (hδ : 4 * δ ≤ unit * β) (hv : v ≤ n) :
    unit * v + unit * β ≤ ℓ * sp - 2 * δ := by
  have hnv := mul_le_mul_of_nonneg_left hv hu
  have hbu := mul_le_mul_of_nonneg_left hβ hu
  have hsp := mul_le_mul_of_nonneg_left hband hℓ
  nlinarith only [hnv, hbu, hsp, hunit, hδ, hu]

/-- Palette preparation only needs rounding small compared with the
native unit. Its error need not be paid by the narrower tracking slack. -/
theorem palette_parent_exponent_gap_of_small_error (ℓ unit β sp δ v n : ℝ)
    (hℓ : 0 ≤ ℓ) (hu : 0 ≤ unit) (hβ : β ≤ 1)
    (hband : 1 / 8 ≤ sp) (hunit : unit * (n + 2) ≤ ℓ / 8)
    (hδ : 2 * δ ≤ unit) (hv : v ≤ n) :
    unit * v + unit * β ≤ ℓ * sp - 2 * δ := by
  have hnv := mul_le_mul_of_nonneg_left hv hu
  have hbu := mul_le_mul_of_nonneg_left hβ hu
  have hsp := mul_le_mul_of_nonneg_left hband hℓ
  nlinarith only [hnv, hbu, hsp, hunit, hδ]

namespace SourceData

variable {W : ℕ} {p : PathData W} (D : SourceData p)

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The parent's physical minor column is below the tested native
velocity width, as required by `linear_native_palette_cap`. -/
theorem parent_palette_minor_column
    (hNk : 1 ≤ Nk) (hL : 0 ≤ L) (unit β H v : ℝ) (hH : 0 < H)
    (hframe : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hHpow : H = Nk ^ (unit * L * β))
    (hfull : D.q₀ / H ≤ r₁ (p.frame D.parent))
    (hgap : unit * v + unit * β ≤ ℓ * sg D.i₀ - 2 * δ₀) (e : Fin 2) :
    |(D.q₀⁻¹ • D.D₀) e 1| ≤ (Nk ^ (unit * L)) ^ (-v) := by
  have hN0 : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  let a := (Nk ^ (unit * L)) ^ (-v)
  have ha : a / H = Nk ^ (-((unit * v + unit * β) * L)) := by
    dsimp only [a]
    rw [← Real.rpow_mul hN0.le, hHpow, ← Real.rpow_sub hN0]
    congr 1
    ring
  have hpow : Nk ^ (-((ℓ * sg D.i₀ - 2 * δ₀) * L)) ≤ a / H := by
    rw [ha]
    apply Real.rpow_le_rpow_of_exponent_le hNk
    have hh := mul_le_mul_of_nonneg_right hgap hL
    nlinarith only [hh]
  have harea : |(p.frame D.parent).det| ≤ D.q₀ ^ 2 * a / H := by
    calc
      _ ≤ D.q₀ ^ 2 * Nk ^ (-((ℓ * sg D.i₀ - 2 * δ₀) * L)) := D.parent_normalized_area hp hNk
      _ ≤ D.q₀ ^ 2 * (a / H) := mul_le_mul_of_nonneg_left hpow (sq_nonneg D.q₀)
      _ = _ := by ring
  rw [hframe]
  exact MajorFrame.normalized_minor_column_le (p.frame D.parent) (hp.chart D.parent).1
    D.q₀ H a D.q₀_pos hH hfull harea e

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
