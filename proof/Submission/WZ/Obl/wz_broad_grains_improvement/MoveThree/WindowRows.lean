-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WindowRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WindowRows.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, WindowRows.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.WindowFilling

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory

def windowRows {κ : Type*} {n N : ℕ} (Y : κ → Fin n → Set V)
    (D : κ → Fin N → Set V) (p : κ × Fin N) (i : Fin n) : Set V :=
  Y p.1 i ∩ D p.1 p.2

theorem window_rows_measurable {κ : Type*} {n N : ℕ}
    (Y : κ → Fin n → Set V) (D : κ → Fin N → Set V)
    (hY : ∀ k i, MeasurableSet (Y k i)) (hD : ∀ k j, MeasurableSet (D k j))
    (p : κ × Fin N) (i : Fin n) : MeasurableSet (windowRows Y D p i) :=
  (hY p.1 i).inter (hD p.1 p.2)

/-- A covering family of windows does not decrease total incidence mass.
Overlaps may duplicate rows; a later colour selection controls this. -/
theorem window_rows_mass {κ : Type*} [Fintype κ] {n N : ℕ}
    (Y : κ → Fin n → Set V) (D : κ → Fin N → Set V)
    (hcover : ∀ k i, Y k i ⊆ ⋃ j, D k j) :
    (∑ k, ∑ i, μ (Y k i)) ≤ ∑ p : κ × Fin N, ∑ i, μ (windowRows Y D p i) := by
  have hone (k : κ) (i : Fin n) : μ (Y k i) ≤ ∑ j, μ (Y k i ∩ D k j) := by
    have hcov : Y k i ⊆ ⋃ j, Y k i ∩ D k j := by
      intro p hp
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover k i hp)
      exact mem_iUnion.mpr ⟨j, hp, hj⟩
    exact (measure_mono hcov).trans (by simpa using measure_iUnion_le (fun j => Y k i ∩ D k j))
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ => hone k i

/-- The row cost of `N` common windows is at most `N` times the original
occupied-row cost, regardless of how the row mass is distributed. -/
theorem window_rows_count {κ : Type*} [Fintype κ] {n N : ℕ}
    (Y : κ → Fin n → Set V) (D : κ → Fin N → Set V) :
    (∑ p : κ × Fin N, q n {i | (windowRows Y D p i).Nonempty}) ≤
      (N : ℝ) * ∑ k, q n {i | (Y k i).Nonempty} := by
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ k, ∑ _j : Fin N, q n {i | (Y k i).Nonempty} := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact Nat.cast_le.mpr (Set.ncard_le_ncard
        (fun i hi => hi.mono inter_subset_left) (Set.toFinite _))
    _ = _ := by simp [← Finset.mul_sum]

/-- Pointwise angular bounds survive every common spatial window. -/
theorem window_rows_cap {κ : Type*} {n N : ℕ}
    (Y : κ → Fin n → Set V) (D : κ → Fin N → Set V)
    (v : Fin n → V) (p : κ × Fin N) (x u : V) (r B : ℝ) (hB : 0 ≤ B)
    (hcap : q n {i | x ∈ Y p.1 i ∧
        WangZahlLot.Obl.wz_measurable_angular_selection.pd (v i) u ≤ r} ≤
      B * q n {i | x ∈ Y p.1 i}) :
    q n {i | x ∈ windowRows Y D p i ∧
        WangZahlLot.Obl.wz_measurable_angular_selection.pd (v i) u ≤ r} ≤
      B * q n {i | x ∈ windowRows Y D p i} :=
  WangZahlLot.Obl.wz_move_two_dense_broad_prisms.broad_common_cut (D p.1 p.2) hB hcap

/-- One of the seventeen axial residue classes carries at least a
seventeenth of every finite aggregate weight. -/
theorem axial_color_mass {κ : Type*} [Fintype κ] {N : ℕ}
    (w : κ × Fin N → ENNReal) :
    ∃ r : Fin 17, (∑ p, w p) ≤
      17 * ∑ p, if (p.2.val % 17) = r.val then w p else 0 := by
  classical
  let color : κ × Fin N → Fin 17 := fun p => ⟨p.2.val % 17, Nat.mod_lt _ (by decide)⟩
  let weight : Fin 17 → ENNReal := fun r => ∑ p, if color p = r then w p else 0
  have hsum : ∑ r, weight r = ∑ p, w p := by
    dsimp only [weight]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  refine ⟨r, ?_⟩
  calc
    _ = ∑ r', weight r' := hsum.symm
    _ ≤ ∑ _r' : Fin 17, weight r := Finset.sum_le_sum fun r' hr' => hr r' hr'
    _ = 17 * weight r := by simp [nsmul_eq_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      have he : color p = r ↔ p.2.val % 17 = r.val := Fin.ext_iff
      simp only [he]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
