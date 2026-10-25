-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.RectangleGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FiniteCells

/-! Finite representatives in an anisotropic two-coordinate slope rectangle. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- Normalize each side of a rectangle before applying the finite cube grid. -/
theorem rectangle_grid_representatives {n M : ℕ} (hn : 0 < n)
    (p : Fin n → Fin 2 → ℝ) (A : Fin 2 → ℝ) (hA : ∀ j, 0 < A j)
    (hp : ∀ i j, |p i j| ≤ A j) {s : ℝ} (hs : 0 < s) (hM : 1 ≤ M*s) :
    ∃ ref : Fin ((2*M+1)^2) → Fin n,
      ∀ i, ∃ k, ∀ j, |p i j - p (ref k) j| < s*A j := by
  let q : Fin n → Fin 2 → ℝ := fun i j => p i j / A j
  have hq : ∀ i j, |q i j| ≤ M*s := by
    intro i j
    calc
      _ = |p i j| / A j := by change |p i j / A j| = _; rw [abs_div, abs_of_pos (hA j)]
      _ ≤ 1 := (div_le_one (hA j)).mpr (hp i j)
      _ ≤ M*s := hM
  obtain ⟨K, hK, ref, href⟩ := wz_clustered_cover_volume_gain.finite_grid_representatives hn q hs hq
  subst K
  refine ⟨ref, fun i => ?_⟩
  obtain ⟨k, hk⟩ := href i
  refine ⟨k, fun j => ?_⟩
  have hh := hk j
  change |p i j / A j - p (ref k) j / A j| < s at hh
  rw [← sub_div, abs_div, abs_of_pos (hA j)] at hh
  exact (div_lt_iff₀ (hA j)).mp hh

/-- A rectangle can be covered by fewer than `(2/s+3)^2` normalized cells. -/
theorem rectangle_grid_size {s : ℝ} (hs : 0 < s) :
    1 ≤ (⌈s⁻¹⌉₊ : ℝ)*s ∧ (((2*⌈s⁻¹⌉₊+1)^2 : ℕ) : ℝ) ≤ (2/s+3)^2 := by
  have hceil := Nat.le_ceil (s⁻¹)
  have hceil' := Nat.ceil_lt_add_one (show 0 ≤ s⁻¹ by positivity)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hceil hs.le
    rwa [inv_mul_cancel₀ hs.ne'] at hh
  · push_cast
    have he : (2 : ℝ)/s = 2*s⁻¹ := by ring
    rw [he]
    apply pow_le_pow_left₀ (by positivity)
    linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
