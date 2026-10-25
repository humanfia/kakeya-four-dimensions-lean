-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreGeometry.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreFrame

/-!
# Geometry of frame cells and fiber witnesses

Points of one frame cell are close in normalized base coordinates; a witness
line whose velocity lies in the narrow bin of the row direction drifts slowly
in the transverse frame coordinate.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set

theorem frameOf_zero_eq (v₁ v₂ : ℝ) (u : Fin 2 → ℝ) :
    frameOf v₁ v₂ u 0 = (v₂ * u 0 - u 1) / (v₂ - v₁) := by
  simp [frameOf, Cart.cartesianFrameCoordinates]

theorem frameOf_one_eq (v₁ v₂ : ℝ) (u : Fin 2 → ℝ) :
    frameOf v₁ v₂ u 1 = (u 1 - v₁ * u 0) / (v₂ - v₁) := by
  simp [frameOf, Cart.cartesianFrameCoordinates]

/-- Two normalized points whose frame coordinates are `ξ`-close. -/
theorem base_close_of_frame_close {v₁ v₂ Λ ξ : ℝ} (hsep : v₂ ≠ v₁)
    (hv₁ : |v₁| ≤ Λ + 1) (hv₂ : |v₂| ≤ Λ + 1) (u u' : Fin 2 → ℝ)
    (h0 : |frameOf v₁ v₂ u 0 - frameOf v₁ v₂ u' 0| ≤ ξ)
    (h1 : |frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1| ≤ ξ) :
    |u 0 - u' 0| ≤ 2 * ξ ∧ |u 1 - u' 1| ≤ 2 * (Λ + 1) * ξ := by
  have ht := frameOf_time hsep u
  have ht' := frameOf_time hsep u'
  have hs := frameOf_space hsep u
  have hs' := frameOf_space hsep u'
  constructor
  · rw [← ht, ← ht']
    calc |frameOf v₁ v₂ u 0 + frameOf v₁ v₂ u 1 - (frameOf v₁ v₂ u' 0 + frameOf v₁ v₂ u' 1)|
        = |(frameOf v₁ v₂ u 0 - frameOf v₁ v₂ u' 0) + (frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1)| := by
          ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  · rw [← hs, ← hs']
    have e : v₁ * frameOf v₁ v₂ u 0 + v₂ * frameOf v₁ v₂ u 1 -
        (v₁ * frameOf v₁ v₂ u' 0 + v₂ * frameOf v₁ v₂ u' 1) =
        v₁ * (frameOf v₁ v₂ u 0 - frameOf v₁ v₂ u' 0) +
          v₂ * (frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1) := by ring
    rw [e]
    have hξ : 0 ≤ ξ := (abs_nonneg _).trans h0
    calc _ ≤ |v₁ * (frameOf v₁ v₂ u 0 - frameOf v₁ v₂ u' 0)| +
          |v₂ * (frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1)| := abs_add_le _ _
      _ = |v₁| * |frameOf v₁ v₂ u 0 - frameOf v₁ v₂ u' 0| +
          |v₂| * |frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1| := by rw [abs_mul, abs_mul]
      _ ≤ (Λ + 1) * ξ + (Λ + 1) * ξ := by
          have hΛ1 : 0 ≤ Λ + 1 := (abs_nonneg _).trans hv₁
          gcongr
      _ = 2 * (Λ + 1) * ξ := by ring

/-- Same-time points: the transverse frame coordinate controls the base distance. -/
theorem base_close_of_same_time {v₁ v₂ Λ ξ : ℝ} (hsep : v₂ ≠ v₁)
    (hv₁ : |v₁| ≤ Λ + 1) (hv₂ : |v₂| ≤ Λ + 1) (u u' : Fin 2 → ℝ) (ht : u 0 = u' 0)
    (h1 : |frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1| ≤ ξ) :
    |u 1 - u' 1| ≤ 2 * (Λ + 1) * ξ := by
  rw [frameOf_one_eq, frameOf_one_eq, ht] at h1
  have hne : v₂ - v₁ ≠ 0 := sub_ne_zero.mpr hsep
  have e : (u 1 - v₁ * u' 0) / (v₂ - v₁) - (u' 1 - v₁ * u' 0) / (v₂ - v₁) =
      (u 1 - u' 1) / (v₂ - v₁) := by field_simp; ring
  rw [e, abs_div] at h1
  have hd : |v₂ - v₁| ≤ 2 * (Λ + 1) := (abs_sub _ _).trans (by linarith)
  have hpos : 0 < |v₂ - v₁| := abs_pos.mpr hne
  have h2 := (div_le_iff₀ hpos).mp h1
  have hξ : 0 ≤ ξ := (div_nonneg (abs_nonneg _) hpos.le).trans h1
  calc |u 1 - u' 1| ≤ ξ * |v₂ - v₁| := h2
    _ ≤ ξ * (2 * (Λ + 1)) := mul_le_mul_of_nonneg_left hd hξ
    _ = 2 * (Λ + 1) * ξ := by ring

/-- A line of velocity `V` moves its transverse frame coordinate at rate
`(V - v₁) / (v₂ - v₁)` in normalized time. -/
theorem frameOf_one_line {v₁ v₂ : ℝ} (hsep : v₂ ≠ v₁) (η₀ V τ τ' : ℝ) :
    frameOf v₁ v₂ ![τ', η₀ + V * τ'] 1 - frameOf v₁ v₂ ![τ, η₀ + V * τ] 1 =
      (V - v₁) * (τ' - τ) / (v₂ - v₁) := by
  rw [frameOf_one_eq, frameOf_one_eq]
  have hne : v₂ - v₁ ≠ 0 := sub_ne_zero.mpr hsep
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- Points close in base coordinates are close in the transverse frame coordinate. -/
theorem frame_one_close {v₁ v₂ Λ δ : ℝ} (hsep : 1 / Λ ≤ |v₂ - v₁|) (hΛ : 0 < Λ)
    (hv₁ : |v₁| ≤ Λ + 1) (u u' : Fin 2 → ℝ) (h0 : |u 0 - u' 0| ≤ δ) (h1 : |u 1 - u' 1| ≤ δ) :
    |frameOf v₁ v₂ u 1 - frameOf v₁ v₂ u' 1| ≤ Λ * (Λ + 2) * δ := by
  have hpos : 0 < |v₂ - v₁| := lt_of_lt_of_le (by positivity) hsep
  have hne : v₂ - v₁ ≠ 0 := abs_pos.mp hpos
  rw [frameOf_one_eq, frameOf_one_eq]
  have e : (u 1 - v₁ * u 0) / (v₂ - v₁) - (u' 1 - v₁ * u' 0) / (v₂ - v₁) =
      ((u 1 - u' 1) - v₁ * (u 0 - u' 0)) / (v₂ - v₁) := by field_simp; ring
  rw [e, abs_div]
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h0
  have hnum : |(u 1 - u' 1) - v₁ * (u 0 - u' 0)| ≤ (Λ + 2) * δ := by
    calc _ ≤ |u 1 - u' 1| + |v₁ * (u 0 - u' 0)| := abs_sub _ _
      _ = |u 1 - u' 1| + |v₁| * |u 0 - u' 0| := by rw [abs_mul]
      _ ≤ δ + (Λ + 1) * δ := by gcongr
      _ = (Λ + 2) * δ := by ring
  have hinv : 1 / |v₂ - v₁| ≤ Λ := by
    rw [div_le_iff₀ hpos]
    have := (div_le_iff₀ hΛ).mp (by simpa using hsep : 1 / Λ ≤ |v₂ - v₁|)
    linarith [mul_comm Λ |v₂ - v₁|]
  calc |(u 1 - u' 1) - v₁ * (u 0 - u' 0)| / |v₂ - v₁|
      = |(u 1 - u' 1) - v₁ * (u 0 - u' 0)| * (1 / |v₂ - v₁|) := by ring
    _ ≤ (Λ + 2) * δ * Λ := mul_le_mul hnum hinv (by positivity) (by positivity)
    _ = Λ * (Λ + 2) * δ := by ring

end Submission.Obl.k4_scalar_grid_cartesian_field
