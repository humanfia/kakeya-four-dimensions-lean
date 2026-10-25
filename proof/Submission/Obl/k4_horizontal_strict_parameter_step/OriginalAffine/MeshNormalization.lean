/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/MeshNormalization.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/MeshNormalization.lean.
   This generic kernel uses original finite cell caps and witness mass only. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.TriangularCoordinates
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set

noncomputable def unitGridTag (H : ℕ) (hH : 0 < H) (u : ℝ) : Fin H :=
  ⟨min ⌊(H : ℝ) * u⌋₊ (H - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hH zero_lt_one)⟩

lemma unitGridTag_round {H : ℕ} (hH : 0 < H) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |(unitGridTag H hH u : ℕ) - (H : ℝ) * u| ≤ 1 := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hnonneg : 0 ≤ (H : ℝ) * u := mul_nonneg hH'.le hu.1
  by_cases hu1 : u < 1
  · have hfl : ⌊(H : ℝ) * u⌋₊ < H := (Nat.floor_lt hnonneg).mpr (by nlinarith)
    have hle : ⌊(H : ℝ) * u⌋₊ ≤ H - 1 := by
      simpa only [Nat.pred_eq_sub_one] using Nat.le_pred_of_lt hfl
    change |(min ⌊(H : ℝ) * u⌋₊ (H - 1) : ℕ) - (H : ℝ) * u| ≤ 1
    rw [min_eq_left hle, abs_sub_comm]
    exact Nat.abs_sub_floor_le hnonneg
  · have hueq : u = 1 := le_antisymm hu.2 (not_lt.mp hu1)
    subst u
    simp only [unitGridTag, mul_one, Nat.floor_natCast]
    rw [min_eq_right (Nat.sub_le H 1), Nat.cast_sub hH]
    norm_num

lemma triangularCoordinates_mem_unit {t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (z : Fin 3 → ℝ)
    (hbox : |z 0 - t₀| ≤ r₀ ∧
      |z 1 - z₀ - l₁ * (z 0 - t₀)| ≤ r₁ ∧
      |z 2 - y₀ - l₂ * (z 0 - t₀) - l₃ * (z 1 - z₀)| ≤ r₂) :
    ∀ j, triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ z j ∈ Icc (0 : ℝ) 1 := by
  have hunit (x r : ℝ) (hr : 0 < r) (hx : |x| ≤ r) :
      (1 + x / r) / 2 ∈ Icc (0 : ℝ) 1 := by
    have hlo : -1 ≤ x / r := (le_div_iff₀ hr).mpr (by linarith [(abs_le.mp hx).1])
    have hhi : x / r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith [(abs_le.mp hx).2])
    constructor <;> linarith
  intro j
  fin_cases j
  · exact hunit _ _ hr₀ hbox.1
  · exact hunit _ _ hr₁ hbox.2.1
  · exact hunit _ _ hr₂ hbox.2.2

/-- Coefficients of an affine function in the normalized triangular coordinates. -/
noncomputable def triangularAffineCoefficients
    (t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ c : ℝ) (g : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![c + g 0 * (t₀ - r₀) + g 1 * (z₀ - l₁ * r₀ - r₁) +
      g 2 * (y₀ - l₂ * r₀ - l₃ * l₁ * r₀ - l₃ * r₁ - r₂),
    2 * r₀ * (g 0 + l₁ * g 1 + (l₂ + l₃ * l₁) * g 2),
    2 * r₁ * (g 1 + l₃ * g 2), 2 * r₂ * g 2]

lemma triangular_affine_identity
    (t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ c : ℝ) (g z : Fin 3 → ℝ)
    (hr₀ : r₀ ≠ 0) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    let L := triangularAffineCoefficients t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ c g
    c + ∑ j : Fin 3, g j * z j =
      L 0 + ∑ j : Fin 3, L j.succ *
        triangularCoordinates t₀ z₀ y₀ l₁ l₂ l₃ r₀ r₁ r₂ z j := by
  simp only [Fin.sum_univ_three]
  dsimp [triangularAffineCoefficients, triangularCoordinates]
  field_simp
  ring

end Submission.Obl.k4_horizontal_strict_parameter_step
