-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/RoundGrid.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/RoundGrid.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Mathlib

/-!
# A symmetric real grid and rounding to it

The grid `ξ ℤ ∩ [-ξ R, ξ R]` used for the Cartesian interpolation of the
physical field: its points are `ξ`-separated, it has `2 R + 1` points, and a
real number of modulus at most `ξ R` lies within `ξ / 2` of its rounding.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

noncomputable section

/-- The symmetric grid `ξ ℤ ∩ [-ξ R, ξ R]`. -/
def symGrid (ξ : ℝ) (R : ℕ) : Finset ℝ :=
  (Finset.Icc (-(R : ℤ)) R).image (fun k : ℤ => ξ * k)

theorem mem_symGrid {ξ : ℝ} {R : ℕ} {x : ℝ} :
    x ∈ symGrid ξ R ↔ ∃ k : ℤ, -(R : ℤ) ≤ k ∧ k ≤ R ∧ ξ * k = x := by
  simp [symGrid, Finset.mem_Icc, and_assoc]

theorem zero_mem_symGrid (ξ : ℝ) (R : ℕ) : (0 : ℝ) ∈ symGrid ξ R :=
  mem_symGrid.mpr ⟨0, by simp, by simp, by simp⟩

scoped instance (ξ : ℝ) (R : ℕ) : Nonempty (symGrid ξ R) := ⟨⟨0, zero_mem_symGrid ξ R⟩⟩

theorem card_symGrid {ξ : ℝ} (hξ : 0 < ξ) (R : ℕ) : (symGrid ξ R).card = 2 * R + 1 := by
  rw [symGrid, Finset.card_image_of_injective]
  · rw [Int.card_Icc]
    omega
  · intro a b hab
    have := mul_left_cancel₀ hξ.ne' hab
    exact_mod_cast this

theorem abs_le_of_mem_symGrid {ξ : ℝ} (hξ : 0 ≤ ξ) {R : ℕ} {x : ℝ} (hx : x ∈ symGrid ξ R) :
    |x| ≤ ξ * R := by
  obtain ⟨k, hk1, hk2, rfl⟩ := mem_symGrid.mp hx
  rw [abs_mul, abs_of_nonneg hξ]
  apply mul_le_mul_of_nonneg_left _ hξ
  have : |k| ≤ (R : ℤ) := abs_le.mpr ⟨hk1, hk2⟩
  have h' : ((|k| : ℤ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast this
  simpa [Int.cast_abs] using h'

theorem symGrid_sep {ξ : ℝ} (hξ : 0 < ξ) (R : ℕ) :
    ∀ x ∈ symGrid ξ R, ∀ y ∈ symGrid ξ R, x ≠ y → ξ ≤ dist x y := by
  intro x hx y hy hxy
  obtain ⟨a, -, -, rfl⟩ := mem_symGrid.mp hx
  obtain ⟨b, -, -, rfl⟩ := mem_symGrid.mp hy
  have hab : a ≠ b := by
    rintro rfl
    exact hxy rfl
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hξ]
  have h1 : (1 : ℝ) ≤ |(a : ℝ) - b| := by
    have : (1 : ℤ) ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hab)
    have h' : ((1 : ℤ) : ℝ) ≤ ((|a - b| : ℤ) : ℝ) := by exact_mod_cast this
    simpa [Int.cast_abs, Int.cast_sub] using h'
  nlinarith

/-- The clamped index of the nearest grid point. -/
def gridIndex (ξ : ℝ) (R : ℕ) (y : ℝ) : ℤ := max (-(R : ℤ)) (min R (round (y / ξ)))

theorem gridIndex_mem (ξ : ℝ) (R : ℕ) (y : ℝ) :
    ξ * (gridIndex ξ R y : ℝ) ∈ symGrid ξ R := by
  refine mem_symGrid.mpr ⟨gridIndex ξ R y, ?_, ?_, rfl⟩
  · exact le_max_left _ _
  · exact max_le (by omega) (min_le_left _ _)

/-- Rounding to the grid. -/
def roundGrid (ξ : ℝ) (R : ℕ) (y : ℝ) : symGrid ξ R :=
  ⟨ξ * (gridIndex ξ R y : ℝ), gridIndex_mem ξ R y⟩

theorem gridIndex_eq_round {ξ : ℝ} (hξ : 0 < ξ) {R : ℕ} {y : ℝ} (hy : |y| ≤ ξ * R) :
    gridIndex ξ R y = round (y / ξ) := by
  have hyR : |y / ξ| ≤ R := by
    rw [abs_div, abs_of_pos hξ, div_le_iff₀ hξ]
    linarith [mul_comm ξ (R : ℝ)]
  have hmono : ∀ a b : ℝ, a ≤ b → round a ≤ round b := by
    intro a b hab
    rw [round_eq, round_eq]
    exact Int.floor_le_floor (by linarith)
  have hlo : -(R : ℤ) ≤ round (y / ξ) := by
    have h1 : round (((-(R : ℤ)) : ℤ) : ℝ) ≤ round (y / ξ) :=
      hmono _ _ (by push_cast; linarith [(abs_le.mp hyR).1])
    rwa [round_intCast] at h1
  have hhi : round (y / ξ) ≤ (R : ℤ) := by
    have h1 : round (y / ξ) ≤ round ((R : ℕ) : ℝ) := hmono _ _ (abs_le.mp hyR).2
    rwa [round_natCast] at h1
  unfold gridIndex
  rw [min_eq_right hhi, max_eq_right hlo]

theorem abs_sub_roundGrid_le {ξ : ℝ} (hξ : 0 < ξ) {R : ℕ} {y : ℝ} (hy : |y| ≤ ξ * R) :
    |y - (roundGrid ξ R y : ℝ)| ≤ ξ / 2 := by
  simp only [roundGrid]
  rw [gridIndex_eq_round hξ hy]
  have h := abs_sub_round (y / ξ)
  have hy' : y - ξ * (round (y / ξ) : ℝ) = ξ * (y / ξ - round (y / ξ)) := by
    field_simp
  rw [hy', abs_mul, abs_of_pos hξ]
  nlinarith

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
