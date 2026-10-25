/- Adapted from this LOT tree o218, branch x0950, commit 5227dd4c,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/KeyFrameCoordinates.lean. Original attribution, when present, is preserved below. -/

import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.CellFrame
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients

/- The key-domain conventions are adapted from this LOT tree o274, x0969,
commit c6776fd2432c9c61c32e60acb489ef2058ab217b,
Submission/Obl/k4_wide_three_layer_scalar_inputs/Inherited/Native/Keys.lean.
That file is inlined from this LOT tree o250, x0879, commit
c77c1a90bc277c8885ed3af05e20668071ee3318,
Submission/Obl/k4_horizontal_wide_interval_return/Native/Keys.lean.
The coordinate identities and bounds below are new proofs for the o218 frame. -/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs
namespace KeyFrame

open Submission.Obl.k4_fixed_budget_quadratic_recovery
noncomputable section

/-- The representative intercept/velocity motion of the original short key. -/
def keyZ (Zk Vk t : ℝ) : ℝ := Zk + t * Vk

/-- The key transverse chart, with its slice coordinate centered at one quarter. -/
def keyY (m q Yk Zk τ y : ℝ) : ℝ := Yk + 2 * m * (y - 1 / 4) - q * τ * Zk

/-- The zero-transverse-coordinate graph of the original true cell. -/
def baseY (F : CellFrame) (t Z : ℝ) : ℝ := F.c 2 + t * F.c 3 + F.c 4 * Z

/-- The key slice coordinate of that true-cell graph. -/
def beta (F : CellFrame) (Zk Yk t Z : ℝ) : ℝ :=
  1 / 4 + (baseY F t Z - Yk + (t - F.t₀) * Zk) / (2 * F.q * F.g)

/-- Its affine coefficients in normalized time on one fixed key motion. -/
def chartBeta (F : CellFrame) (Zk Vk Yk : ℝ) : Fin 2 → ℝ :=
  ![1 / 4 + (baseY F F.t₀ (keyZ Zk Vk F.t₀) - Yk) / (2 * F.q * F.g),
    (F.c 3 + F.c 4 * Vk + Zk) / (2 * F.g)]

/-- Its affine coefficients in the normalized true-cell coordinates `(τ,zZ)`. -/
def frameBeta (F : CellFrame) (Zk Yk : ℝ) : Fin 3 → ℝ :=
  ![1 / 4 + (baseY F F.t₀ (F.c 0 + F.t₀ * F.c 1) - Yk) / (2 * F.q * F.g),
    (F.c 3 + F.c 4 * F.c 1 + Zk) / (2 * F.g), F.c 4 / (2 * F.g)]

/-- The nonconstant transverse coefficients of a normalized key discrepancy. -/
def f1 (r : Fin 6 → ℝ) (τ y : ℝ) : ℝ := (r 2 + r 4 * τ + 2 * r 5 * y) / 2

def f2 (r : Fin 6 → ℝ) : ℝ := r 5 / 4

/-- The two coefficients of `f1` along the representative motion. -/
def chartF1 (F : CellFrame) (Zk Vk Yk : ℝ) (r : Fin 6 → ℝ) : Fin 2 → ℝ :=
  ![r 2 / 2 + r 5 * chartBeta F Zk Vk Yk 0,
    r 4 / 2 + r 5 * chartBeta F Zk Vk Yk 1]

/-- The three coefficients of `f1` in the full true-cell coordinates. -/
def frameF1 (F : CellFrame) (Zk Yk : ℝ) (r : Fin 6 → ℝ) : Fin 3 → ℝ :=
  ![r 2 / 2 + r 5 * frameBeta F Zk Yk 0,
    r 4 / 2 + r 5 * frameBeta F Zk Yk 1, r 5 * frameBeta F Zk Yk 2]

theorem keyY_beta (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (Zk Yk τ Z U : ℝ) :
    keyY (F.q * F.g) F.q Yk Zk τ (beta F Zk Yk (F.t₀ + F.q * τ) Z + U / 2) =
      baseY F (F.t₀ + F.q * τ) Z + F.q * F.g * U := by
  unfold keyY beta
  field_simp
  <;> ring

theorem beta_chart (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (Zk Vk Yk τ : ℝ) :
    beta F Zk Yk (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ)) =
      chartBeta F Zk Vk Yk 0 + τ * chartBeta F Zk Vk Yk 1 := by
  simp [beta, chartBeta, baseY, keyZ]
  field_simp
  <;> ring

theorem beta_frame (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (Zk Yk τ z : ℝ) :
    beta F Zk Yk (F.t₀ + F.q * τ)
        (F.c 0 + (F.t₀ + F.q * τ) * F.c 1 + F.q * z) =
      frameBeta F Zk Yk 0 + τ * frameBeta F Zk Yk 1 + z * frameBeta F Zk Yk 2 := by
  simp [beta, frameBeta, baseY]
  field_simp
  <;> ring

theorem beta_change_Z (F : CellFrame) (Zk Yk t Z Z' : ℝ) :
    beta F Zk Yk t Z - beta F Zk Yk t Z' =
      F.c 4 * (Z - Z') / (2 * F.q * F.g) := by
  unfold beta baseY
  ring

/-- Replacing the true coordinate by the key motion affects only `f1`, by
this exact term. No normalization or reference floor is part of the identity. -/
theorem f1_change_Z (F : CellFrame) (r : Fin 6 → ℝ) (Zk Yk t τ Z Z' : ℝ) :
    f1 r τ (beta F Zk Yk t Z) - f1 r τ (beta F Zk Yk t Z') =
      r 5 * F.c 4 * (Z - Z') / (2 * F.q * F.g) := by
  have h := beta_change_Z F Zk Yk t Z Z'
  unfold f1
  linear_combination r 5 * h

theorem f1_chart (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (r : Fin 6 → ℝ) (Zk Vk Yk τ : ℝ) :
    f1 r τ (beta F Zk Yk (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))) =
      chartF1 F Zk Vk Yk r 0 + τ * chartF1 F Zk Vk Yk r 1 := by
  rw [beta_chart F hq hg]
  simp [f1, chartF1]
  ring

theorem f1_frame (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (r : Fin 6 → ℝ) (Zk Yk τ z : ℝ) :
    f1 r τ (beta F Zk Yk (F.t₀ + F.q * τ)
      (F.c 0 + (F.t₀ + F.q * τ) * F.c 1 + F.q * z)) =
      frameF1 F Zk Yk r 0 + τ * frameF1 F Zk Yk r 1 + z * frameF1 F Zk Yk r 2 := by
  rw [beta_frame F hq hg]
  simp [f1, frameF1]
  ring

/-- Exact transverse Taylor expansion in the short key's quadratic convention. -/
theorem quadratic_key_expansion (r : Fin 6 → ℝ) (τ y U : ℝ) :
    quadraticValue r τ (y + U / 2) = quadraticValue r τ y + f1 r τ y * U + f2 r * U ^ 2 := by
  unfold quadraticValue f1 f2
  ring

end
end KeyFrame
end Submission.Obl.k4_wide_three_layer_scalar_inputs
