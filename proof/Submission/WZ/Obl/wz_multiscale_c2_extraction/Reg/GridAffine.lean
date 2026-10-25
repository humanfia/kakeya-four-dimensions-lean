-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridAffine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.LinearityIteration

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set

/-- Linear interpolation of prescribed values on an arbitrary real grid. -/
noncomputable def gridInterpolate (h : ℝ) (u : ℤ → ℝ) (z : ℝ) : ℝ :=
  let j := Int.floor (z / h)
  u j + ((z - (j : ℝ) * h) / h) * (u (j + 1) - u j)

theorem gridInterpolate_at_grid {h : ℝ} (hh : 0 < h) (u : ℤ → ℝ) (j : ℤ) :
    gridInterpolate h u ((j : ℝ) * h) = u j := by
  simp [gridInterpolate, hh.ne']

theorem gridInterpolate_on_cell {h : ℝ} (hh : 0 < h) (u : ℤ → ℝ)
    (j : ℤ) {z : ℝ} (hz : z ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) :
    gridInterpolate h u z =
      u j + ((z - (j : ℝ) * h) / h) * (u (j + 1) - u j) := by
  rcases eq_or_lt_of_le hz.2 with hz' | hz'
  · subst z
    have he : ((j : ℝ) + 1) * h = ((j + 1 : ℤ) : ℝ) * h := by simp
    rw [he, gridInterpolate_at_grid hh]
    push_cast
    field_simp
    <;> ring
  · have hj : Int.floor (z / h) = j := by
      apply Int.floor_eq_iff.mpr
      exact ⟨(le_div_iff₀ hh).mpr hz.1, (div_lt_iff₀ hh).mpr hz'⟩
    simp only [gridInterpolate, hj]

theorem gridInterpolate_affine {h : ℝ} (hh : 0 < h) (u : ℤ → ℝ) :
    AffineOnGrid h (gridInterpolate h u) := by
  intro j
  refine ⟨u j - ((u (j + 1) - u j) / h) * ((j : ℝ) * h),
    (u (j + 1) - u j) / h, ?_⟩
  intro z hz
  rw [gridInterpolate_on_cell hh u j hz]
  ring

/-- Affine functions on nonadjacent grid cells extend to a function affine on
every grid cell. No bound on the slopes is needed. -/
theorem exists_affine_grid_extension {h : ℝ} (hh : 0 < h)
    (J : Set ℤ) (a b : ℤ → ℝ)
    (hsep : ∀ j ∈ J, j + 1 ∉ J) :
    ∃ L : ℝ → ℝ, AffineOnGrid h L ∧
      ∀ j ∈ J, ∀ z ∈ Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
        L z = a j + b j * z := by
  classical
  let u : ℤ → ℝ := fun j =>
    if j ∈ J then a j + b j * ((j : ℝ) * h)
    else if j - 1 ∈ J then a (j - 1) + b (j - 1) * ((j : ℝ) * h)
    else 0
  refine ⟨gridInterpolate h u, gridInterpolate_affine hh u, ?_⟩
  intro j hj z hz
  rw [gridInterpolate_on_cell hh u j hz]
  have hu : u j = a j + b j * ((j : ℝ) * h) := by simp [u, hj]
  have huv : u (j + 1) = a j + b j * (((j : ℝ) + 1) * h) := by
    simp [u, hsep j hj, hj]
  rw [hu, huv]
  field_simp
  <;> ring

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
