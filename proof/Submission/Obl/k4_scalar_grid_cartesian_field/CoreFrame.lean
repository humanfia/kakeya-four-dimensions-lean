-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreFrame.lean.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.CartesianFramePolynomial
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.GridPencils
import Submission.Obl.k4_scalar_grid_cartesian_field.CoreLists

/-!
# The two-velocity frame and its regular grid

Normalized base coordinates `u = ((t, y) - z₀) / h` are written in the frame
of the two directions `(1, v₁)` and `(1, v₂)`; a regular grid of step `ξ`
covers the box `[-Bf, Bf]²` of frame coordinates.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set

/-- Frame coordinates of a normalized base point. -/
noncomputable def frameOf (v₁ v₂ : ℝ) (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  Cart.cartesianFrameCoordinates 0 0 v₁ v₂ (u 0) (u 1)

/-- Number of grid points on one axis. -/
noncomputable def gridSize (Bf ξ : ℝ) : ℕ := ⌈2 * Bf / ξ⌉₊ + 1

scoped instance gridSize_neZero (Bf ξ : ℝ) : NeZero (gridSize Bf ξ) := ⟨by simp [gridSize]⟩

open scoped Submission.Obl.k4_scalar_grid_cartesian_field

/-- Grid positions on one axis. -/
noncomputable def gridPos (Bf ξ : ℝ) (i : Fin (gridSize Bf ξ)) : ℝ := -Bf + ξ * (i : ℝ)

/-- The grid index of a real coordinate (clamped). -/
noncomputable def gridIdx (Bf ξ : ℝ) (x : ℝ) : Fin (gridSize Bf ξ) :=
  ⟨min (⌊(x + Bf) / ξ⌋.toNat) (gridSize Bf ξ - 1), by
    have : 0 < gridSize Bf ξ := Nat.pos_of_neZero _
    omega⟩

theorem measurable_gridIdx (Bf ξ : ℝ) : Measurable (gridIdx Bf ξ) := by
  have hfl : Measurable fun x : ℝ => ⌊(x + Bf) / ξ⌋ :=
    Int.measurable_floor.comp ((measurable_id.add_const Bf).div_const ξ)
  have hf : Measurable fun k : ℤ => (⟨min k.toNat (gridSize Bf ξ - 1), by
      have : 0 < gridSize Bf ξ := Nat.pos_of_neZero _
      omega⟩ : Fin (gridSize Bf ξ)) := measurable_of_countable _
  exact hf.comp hfl

theorem gridIdx_spec {Bf ξ x : ℝ} (hξ : 0 < ξ) (hx : |x| ≤ Bf) :
    gridPos Bf ξ (gridIdx Bf ξ x) ≤ x ∧ x < gridPos Bf ξ (gridIdx Bf ξ x) + ξ := by
  have hxB := abs_le.mp hx
  set k := ⌊(x + Bf) / ξ⌋ with hk
  have hk0 : 0 ≤ k := Int.floor_nonneg.mpr (div_nonneg (by linarith) hξ.le)
  have hkle : (k : ℝ) ≤ (x + Bf) / ξ := Int.floor_le _
  have hklt : (x + Bf) / ξ < k + 1 := Int.lt_floor_add_one _
  have hkn : k.toNat ≤ gridSize Bf ξ - 1 := by
    have h1 : (k : ℝ) ≤ 2 * Bf / ξ := hkle.trans (div_le_div_of_nonneg_right (by linarith) hξ.le)
    have h2 : 2 * Bf / ξ ≤ (⌈2 * Bf / ξ⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (k.toNat : ℝ) ≤ ⌈2 * Bf / ξ⌉₊ := by
      rw [show ((k.toNat : ℕ) : ℝ) = (k : ℝ) by exact_mod_cast Int.toNat_of_nonneg hk0]
      linarith
    have h4 : k.toNat ≤ ⌈2 * Bf / ξ⌉₊ := by exact_mod_cast h3
    simp [gridSize]
    omega
  have hidx : ((gridIdx Bf ξ x : ℕ) : ℝ) = (k : ℝ) := by
    have hval : (gridIdx Bf ξ x : ℕ) = k.toNat := by
      show min (⌊(x + Bf) / ξ⌋.toNat) (gridSize Bf ξ - 1) = k.toNat
      rw [← hk]
      exact min_eq_left hkn
    rw [hval]
    exact_mod_cast Int.toNat_of_nonneg hk0
  unfold gridPos
  rw [hidx]
  constructor
  · have := (le_div_iff₀ hξ).mp hkle
    linarith
  · have := (div_lt_iff₀ hξ).mp hklt
    linarith

theorem gridPos_abs_le {Bf ξ : ℝ} (hξ : 0 < ξ) (hBf : 0 ≤ Bf) (i : Fin (gridSize Bf ξ)) :
    |gridPos Bf ξ i| ≤ Bf + 2 * ξ := by
  unfold gridPos
  have hi : (i : ℕ) ≤ ⌈2 * Bf / ξ⌉₊ := by
    have := i.isLt
    simp [gridSize] at this
    omega
  have hi' : ((i : ℕ) : ℝ) ≤ 2 * Bf / ξ + 1 :=
    (Nat.cast_le.mpr hi).trans (Nat.ceil_lt_add_one (by positivity)).le
  have hiξ : ξ * ((i : ℕ) : ℝ) ≤ 2 * Bf + ξ := by
    calc ξ * ((i : ℕ) : ℝ) ≤ ξ * (2 * Bf / ξ + 1) := mul_le_mul_of_nonneg_left hi' hξ.le
      _ = 2 * Bf + ξ := by field_simp
  have hi0 : 0 ≤ ξ * ((i : ℕ) : ℝ) := by positivity
  rw [abs_le]
  constructor <;> linarith

theorem gridSize_span {Bf ξ : ℝ} (hξ : 0 < ξ) (hBf : 1 ≤ Bf) :
    1 ≤ (gridSize Bf ξ : ℝ) * ξ := by
  have h1 : 2 * Bf / ξ ≤ (⌈2 * Bf / ξ⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (gridSize Bf ξ : ℝ) = (⌈2 * Bf / ξ⌉₊ : ℝ) + 1 := by simp [gridSize]
  have h3 : 2 * Bf ≤ (⌈2 * Bf / ξ⌉₊ : ℝ) * ξ := (div_le_iff₀ hξ).mp h1
  rw [h2]
  nlinarith

theorem gridSize_le {Bf ξ : ℝ} (hξ : 0 < ξ) (hBf : 0 ≤ Bf) :
    (gridSize Bf ξ : ℝ) ≤ 2 * Bf / ξ + 2 := by
  have h2 : (gridSize Bf ξ : ℝ) = (⌈2 * Bf / ξ⌉₊ : ℝ) + 1 := by simp [gridSize]
  have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Bf / ξ by positivity)
  rw [h2]
  linarith

/-- The time reconstruction of normalized frame coordinates. -/
theorem frameOf_time {v₁ v₂ : ℝ} (hsep : v₂ ≠ v₁) (u : Fin 2 → ℝ) :
    frameOf v₁ v₂ u 0 + frameOf v₁ v₂ u 1 = u 0 := by
  have := Cart.cartesianFrame_time_reconstruction 0 0 v₁ v₂ (u 0) (u 1) hsep
  simpa [frameOf] using this

theorem frameOf_space {v₁ v₂ : ℝ} (hsep : v₂ ≠ v₁) (u : Fin 2 → ℝ) :
    v₁ * frameOf v₁ v₂ u 0 + v₂ * frameOf v₁ v₂ u 1 = u 1 := by
  have := Cart.cartesianFrame_space_reconstruction 0 0 v₁ v₂ (u 0) (u 1) hsep
  simpa [frameOf] using this

theorem frameOf_bound {v₁ v₂ K R : ℝ} (hK : 1 ≤ K) (hR : 0 ≤ R) (hv₁ : |v₁| ≤ K)
    (hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|) (u : Fin 2 → ℝ) (hu0 : |u 0| ≤ R)
    (hu1 : |u 1| ≤ R) (i : Fin 2) :
    |frameOf v₁ v₂ u i| ≤ 2 * K ^ 2 * R := by
  have := Cart.cartesianFrame_coordinate_bound 0 0 v₁ v₂ (u 0) (u 1) K R hK hR hv₁ hv₂ hsep
    (by simpa using hu0) (by simpa using hu1) i
  simpa [frameOf] using this

theorem measurable_frameOf (v₁ v₂ : ℝ) : Measurable (frameOf v₁ v₂) := by
  unfold frameOf Cart.cartesianFrameCoordinates
  apply measurable_pi_lambda
  intro i
  have h0 : Measurable fun u : Fin 2 → ℝ => u 0 := measurable_pi_apply 0
  have h1 : Measurable fun u : Fin 2 → ℝ => u 1 := measurable_pi_apply 1
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact (((h0.sub_const 0).const_mul v₂).sub (h1.sub_const 0)).div_const _
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact ((h1.sub_const 0).sub ((h0.sub_const 0).const_mul v₁)).div_const _

theorem measurable_normalizedBase (h : ℝ) (z₀ : Fin 2 → ℝ) :
    Measurable (normalizedBase h z₀) := by
  unfold normalizedBase
  apply measurable_pi_lambda
  intro e
  apply Measurable.div_const
  apply Measurable.sub_const
  have h0 : Measurable fun p : Incidence => p.2 := measurable_snd
  have hy : Measurable fun p : Incidence => scalarY p.1 p.2 := by
    unfold scalarY
    have h1 : Measurable fun p : Incidence => p.1.2 0 :=
      (measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst)
    have h2 : Measurable fun p : Incidence => p.1.2 1 :=
      (measurable_pi_apply 1).comp (measurable_snd.comp measurable_fst)
    exact h1.add (h0.mul h2)
  fin_cases e
  · exact h0
  · exact hy

end Submission.Obl.k4_scalar_grid_cartesian_field
