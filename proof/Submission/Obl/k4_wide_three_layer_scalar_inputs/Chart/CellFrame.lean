/- Adapted from this LOT tree o218, branch x0950, commit 5227dd4c,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/CellFrame.lean. Original attribution, when present, is preserved below. -/

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Normalized coordinates of a true cell and the scalar signal after subtraction

A true label at depth `s` has a time block `[t₀, t₀ + q]`, a tilted box
`|Z - c₀ - t c₁| ≤ K q`, `|Y - c₂ - t c₃ - c₄ Z| ≤ K q g`, and an affine fit
`X ≈ L₀ + L₁ t + L₂ Z + L₃ Y` to width `a`.  In the last step of the wide-interval proposition
(paper `prop:wide-interval`, "Scalar support after subtraction") one subtracts a transverse
polynomial `P_nc = (C₀ + C₁ z_t + C₂ z_Z) U + C₃ U²` from the normalized residual and applies
scalar mesh projection in `(z_t, z_Z)`.  This file fixes the normalized coordinates
`z_t, z_Z, U`, the residual, and the scalar signal, and computes their restrictions to a
trajectory `t ↦ (t, b₀ + t b₃, b₁ + t b₄, b₂ + t b₅)` in normalized time `t = t₀ + q z`:
`z_Z` is affine and the signal is quadratic, with explicit coefficients (`lineCoeffs`), which are
the five coefficients the frozen scalar theorem takes.  Everything is rate-free.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

/-- The data of a true cell frame and a transverse correction. -/
structure CellFrame where
  t₀ : ℝ
  q : ℝ
  g : ℝ
  a : ℝ
  c : Fin 5 → ℝ
  L : Fin 4 → ℝ
  C : Fin 4 → ℝ

namespace CellFrame

variable (F : CellFrame)

/-- Normalized time. -/
noncomputable def zt (t : ℝ) : ℝ := (t - F.t₀) / F.q

/-- Normalized horizontal position. -/
noncomputable def zZ (t Z : ℝ) : ℝ := (Z - F.c 0 - t * F.c 1) / F.q

/-- Normalized transverse position. -/
noncomputable def U (t Z Y : ℝ) : ℝ := (Y - F.c 2 - t * F.c 3 - F.c 4 * Z) / (F.q * F.g)

/-- The affine fit of the true cell. -/
def fit (t Z Y : ℝ) : ℝ := F.L 0 + F.L 1 * t + F.L 2 * Z + F.L 3 * Y

/-- Normalized residual of the hidden coordinate. -/
noncomputable def resid (t Z Y X : ℝ) : ℝ := (X - F.fit t Z Y) / F.a

/-- The transverse correction `(C₀ + C₁ z_t + C₂ z_Z) U + C₃ U²`. -/
noncomputable def Pnc (t Z Y : ℝ) : ℝ :=
  (F.C 0 + F.C 1 * F.zt t + F.C 2 * F.zZ t Z) * F.U t Z Y + F.C 3 * F.U t Z Y ^ 2

/-- The scalar signal after subtracting the transverse correction. -/
noncomputable def sig (t Z Y X : ℝ) : ℝ := F.resid t Z Y X - F.Pnc t Z Y

/-! ### Restriction to a trajectory -/

/-- Affine coefficients of `z_Z` along the trajectory `b`, in normalized time. -/
noncomputable def y₀ (b : Fin 6 → ℝ) : ℝ := (b 0 + F.t₀ * b 3 - F.c 0 - F.t₀ * F.c 1) / F.q
def y₁ (b : Fin 6 → ℝ) : ℝ := b 3 - F.c 1

/-- Affine coefficients of `U` along the trajectory. -/
noncomputable def u₀ (b : Fin 6 → ℝ) : ℝ :=
  ((b 1 - F.c 2 - F.c 4 * b 0) + F.t₀ * (b 4 - F.c 3 - F.c 4 * b 3)) / (F.q * F.g)
noncomputable def u₁ (b : Fin 6 → ℝ) : ℝ := (b 4 - F.c 3 - F.c 4 * b 3) / F.g

/-- Affine coefficients of the residual along the trajectory. -/
noncomputable def r₀ (b : Fin 6 → ℝ) : ℝ :=
  (b 2 - F.L 0 - F.L 2 * b 0 - F.L 3 * b 1 +
    F.t₀ * (b 5 - F.L 1 - F.L 2 * b 3 - F.L 3 * b 4)) / F.a
noncomputable def r₁ (b : Fin 6 → ℝ) : ℝ := F.q * (b 5 - F.L 1 - F.L 2 * b 3 - F.L 3 * b 4) / F.a

/-- The five coefficients `(y₀, y₁, x₀, x₁, x₂)` of the trajectory in the scalar theorem:
`z_Z = y₀ + z y₁` and `sig = x₀ + z x₁ + z² x₂` in normalized time `z`. -/
noncomputable def lineCoeffs (b : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![F.y₀ b, F.y₁ b,
    F.r₀ b - (F.C 0 + F.C 2 * F.y₀ b) * F.u₀ b - F.C 3 * F.u₀ b ^ 2,
    F.r₁ b - ((F.C 0 + F.C 2 * F.y₀ b) * F.u₁ b + (F.C 1 + F.C 2 * F.y₁ b) * F.u₀ b +
      2 * F.C 3 * F.u₀ b * F.u₁ b),
    -((F.C 1 + F.C 2 * F.y₁ b) * F.u₁ b + F.C 3 * F.u₁ b ^ 2)]

variable {F}

theorem zt_line (hq : F.q ≠ 0) (z : ℝ) : F.zt (F.t₀ + F.q * z) = z := by
  unfold zt; field_simp; ring

theorem zZ_line (hq : F.q ≠ 0) (b : Fin 6 → ℝ) (z : ℝ) :
    F.zZ (F.t₀ + F.q * z) (b 0 + (F.t₀ + F.q * z) * b 3) = F.y₀ b + z * F.y₁ b := by
  unfold zZ y₀ y₁; field_simp; ring

theorem U_line (hq : F.q ≠ 0) (hg : F.g ≠ 0) (b : Fin 6 → ℝ) (z : ℝ) :
    F.U (F.t₀ + F.q * z) (b 0 + (F.t₀ + F.q * z) * b 3) (b 1 + (F.t₀ + F.q * z) * b 4) =
      F.u₀ b + z * F.u₁ b := by
  unfold U u₀ u₁; field_simp; ring

theorem resid_line (ha : F.a ≠ 0) (b : Fin 6 → ℝ) (z : ℝ) :
    F.resid (F.t₀ + F.q * z) (b 0 + (F.t₀ + F.q * z) * b 3) (b 1 + (F.t₀ + F.q * z) * b 4)
      (b 2 + (F.t₀ + F.q * z) * b 5) = F.r₀ b + z * F.r₁ b := by
  unfold resid fit r₀ r₁; field_simp; ring

/-- Along a trajectory, the normalized horizontal position is the scalar theorem's affine
parameter `y = b'₀ + z b'₁`. -/
theorem lineCoeffs_y (hq : F.q ≠ 0) (b : Fin 6 → ℝ) (z : ℝ) :
    F.zZ (F.t₀ + F.q * z) (b 0 + (F.t₀ + F.q * z) * b 3) =
      F.lineCoeffs b 0 + z * F.lineCoeffs b 1 := by
  rw [zZ_line hq]; simp [lineCoeffs]

/-- Along a trajectory, the scalar signal is the scalar theorem's quadratic
`x = b'₂ + z b'₃ + z² b'₄`. -/
theorem lineCoeffs_x (hq : F.q ≠ 0) (hg : F.g ≠ 0) (ha : F.a ≠ 0) (b : Fin 6 → ℝ) (z : ℝ) :
    F.sig (F.t₀ + F.q * z) (b 0 + (F.t₀ + F.q * z) * b 3) (b 1 + (F.t₀ + F.q * z) * b 4)
      (b 2 + (F.t₀ + F.q * z) * b 5) =
      F.lineCoeffs b 2 + z * F.lineCoeffs b 3 + z ^ 2 * F.lineCoeffs b 4 := by
  unfold sig Pnc
  rw [resid_line ha, zt_line hq, zZ_line hq, U_line hq hg]
  simp only [lineCoeffs, Matrix.cons_val]
  simp
  ring

end CellFrame

end Submission.Obl.k4_wide_three_layer_scalar_inputs
