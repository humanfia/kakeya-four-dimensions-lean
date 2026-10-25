-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.FiniteCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set

/-- Equal integer cells place two real numbers less than one cell-width apart. -/
theorem abs_sub_lt_of_floor_eq {x y s : ℝ} (hs : 0 < s)
    (h : ⌊x / s⌋ = ⌊y / s⌋) : |x - y| < s := by
  have hxl := Int.floor_le (x / s)
  have hxu := Int.lt_floor_add_one (x / s)
  have hyl := Int.floor_le (y / s)
  have hyu := Int.lt_floor_add_one (y / s)
  rw [h] at hxl hxu
  have hh : |x / s - y / s| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [← sub_div, abs_div, abs_of_pos hs] at hh
  simpa only [one_mul] using (div_lt_iff₀ hs).mp hh

abbrev GridCode (d A : ℕ) := Fin d → ↥(Finset.Icc (-(A : ℤ)) (A : ℤ))

theorem card_gridCode (d A : ℕ) : Fintype.card (GridCode d A) = (2 * A + 1) ^ d := by
  simp only [GridCode, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, Int.card_Icc]
  congr 1
  omega

def gridCodeOf {n d A : ℕ} (p : Fin n → Fin d → ℝ) {s : ℝ} (hs : 0 < s)
    (hb : ∀ i j, |p i j| ≤ A * s) (i : Fin n) : GridCode d A := fun j =>
  ⟨⌊p i j / s⌋, by
    have hdiv : -(A : ℝ) ≤ p i j / s ∧ p i j / s ≤ A := by
      obtain ⟨hl, hu⟩ := abs_le.mp (hb i j)
      constructor
      · apply (le_div_iff₀ hs).mpr
        nlinarith
      · exact (div_le_iff₀ hs).mpr hu
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      simpa only [Int.cast_neg, Int.cast_natCast] using hdiv.1
    · have hh := (Int.floor_le (p i j / s)).trans hdiv.2
      exact_mod_cast hh⟩

/-- A finite family in a coordinate cube has representatives in at most
`(2*A+1)^d` cells. Representatives are actual members of the original family. -/
theorem finite_grid_representatives {n d A : ℕ} (hn : 0 < n)
    (p : Fin n → Fin d → ℝ) {s : ℝ} (hs : 0 < s)
    (hb : ∀ i j, |p i j| ≤ A * s) :
    ∃ K : ℕ, K = (2 * A + 1) ^ d ∧ ∃ ref : Fin K → Fin n,
      ∀ i, ∃ k, ∀ j, |p i j - p (ref k) j| < s := by
  classical
  let code := gridCodeOf p hs hb
  let i₀ : Fin n := ⟨0, hn⟩
  let rep : GridCode d A → Fin n := fun q =>
    if h : ∃ i, code i = q then h.choose else i₀
  have hrep (i : Fin n) : code (rep (code i)) = code i := by
    have hi : ∃ j, code j = code i := ⟨i, rfl⟩
    dsimp only [rep]
    rw [dif_pos hi]
    exact hi.choose_spec
  let eqv := Fintype.equivFin (GridCode d A)
  refine ⟨Fintype.card (GridCode d A), card_gridCode d A, rep ∘ eqv.symm, ?_⟩
  intro i
  refine ⟨eqv (code i), ?_⟩
  intro j
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  apply abs_sub_lt_of_floor_eq hs
  have hh := congrArg (fun q : GridCode d A => (q j).val) (hrep i)
  exact hh.symm

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
