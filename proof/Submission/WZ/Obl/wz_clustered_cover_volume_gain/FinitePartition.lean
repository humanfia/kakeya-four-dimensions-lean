-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.FinitePartition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FiniteCells

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set

/-- A finite family can be partitioned by arbitrary codes, with an actual
member chosen as the representative of every nonempty part. -/
theorem finite_code_partition {n : ℕ} {κ : Type*} (code : Fin n → κ) :
    ∃ N : ℕ, ∃ f : Fin n → Fin N, ∃ ref : Fin N → Fin n,
      (∀ k, f (ref k) = k) ∧
      (∀ i j, f i = f j ↔ code i = code j) := by
  classical
  let C := Finset.univ.image code
  let e := Fintype.equivFin ↥C
  have hex (k : Fin (Fintype.card ↥C)) : ∃ i, code i = (e.symm k).val := by
    exact Finset.mem_image.mp (e.symm k).property |>.imp fun _ h => h.2
  choose ref href using hex
  let f : Fin n → Fin (Fintype.card ↥C) := fun i => e ⟨code i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  refine ⟨Fintype.card ↥C, f, ref, ?_, ?_⟩
  · intro k
    apply e.symm.injective
    apply Subtype.ext
    simpa only [f, Equiv.symm_apply_apply] using href k
  · intro i j
    change e _ = e _ ↔ code i = code j
    rw [e.injective.eq_iff, Subtype.mk.injEq]

lemma floor_difference_bounds {x y s : ℝ} {A : ℕ} (hs : 0 < s)
    (hxy : |x - y| ≤ A * s) :
    -((A + 1 : ℕ) : ℤ) ≤ ⌊x / s⌋ - ⌊y / s⌋ ∧
      ⌊x / s⌋ - ⌊y / s⌋ ≤ ((A + 1 : ℕ) : ℤ) := by
  have hdiv : |x / s - y / s| ≤ A := by
    rw [← sub_div, abs_div, abs_of_pos hs]
    exact (div_le_iff₀ hs).mpr hxy
  obtain ⟨hl, hu⟩ := abs_le.mp hdiv
  have hx0 := Int.floor_le (x / s)
  have hx1 := Int.lt_floor_add_one (x / s)
  have hy0 := Int.floor_le (y / s)
  have hy1 := Int.lt_floor_add_one (y / s)
  constructor
  · have hh : -((A : ℝ) + 1) ≤ (⌊x / s⌋ : ℝ) - (⌊y / s⌋ : ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (⌊x / s⌋ : ℝ) - (⌊y / s⌋ : ℝ) ≤ (A : ℝ) + 1 := by linarith
    exact_mod_cast hh

/-- The number of grid cells meeting a coordinate box is independent of
the location of the box and of the total number of objects. -/
theorem grid_image_card_le {n d A : ℕ} (S : Finset (Fin n))
    (x : Fin n → Fin d → ℝ) (y : Fin d → ℝ) (s : Fin d → ℝ)
    (hs : ∀ j, 0 < s j) (hx : ∀ i ∈ S, ∀ j, |x i j - y j| ≤ A * s j) :
    (S.image (fun i j => ⌊x i j / s j⌋)).card ≤ (2 * (A + 1) + 1) ^ d := by
  classical
  let base : Fin d → ℤ := fun j => ⌊y j / s j⌋
  let shift : GridCode d (A + 1) → (Fin d → ℤ) := fun q j => base j + (q j).val
  have hsub : S.image (fun i j => ⌊x i j / s j⌋) ⊆ Finset.univ.image shift := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    let q : GridCode d (A + 1) := fun j =>
      ⟨⌊x i j / s j⌋ - base j,
        Finset.mem_Icc.mpr (floor_difference_bounds (hs j) (hx i hi j))⟩
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
    ext j
    dsimp [shift, q]
    omega
  calc
    _ ≤ (Finset.univ.image shift).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (GridCode d (A + 1)) := Finset.card_image_le
    _ = _ := card_gridCode _ _

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
