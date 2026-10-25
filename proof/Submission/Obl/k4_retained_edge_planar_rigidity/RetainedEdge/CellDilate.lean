-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/CellDilate.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.Cells

/-!
# Dilating finite planar sets

A dilation by a real factor `c` maps one grid cell into a square of side `|c|` (in cell units),
which meets at most `(2|c| + 2)²` cells. Hence `N(c • U) ≤ (2|c| + 2)² N(U)`, and for `c ≠ 0` the
reverse comparison holds with `c⁻¹`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

/-- The cells that a dilate by `c` of the cell `w` can meet. -/
def dilateCells (c : ℝ) (w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc ⌊c * w.1 - |c|⌋ ⌊c * w.1 + |c|⌋ ×ˢ Finset.Icc ⌊c * w.2 - |c|⌋ ⌊c * w.2 + |c|⌋

theorem card_Icc_floor_le (α β : ℝ) (hαβ : α ≤ β) :
    ((Finset.Icc ⌊α⌋ ⌊β⌋).card : ℝ) ≤ β - α + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le β
  have h2 := Int.lt_floor_add_one α
  have hle : ⌊α⌋ ≤ ⌊β⌋ := Int.floor_mono hαβ
  have hnn : 0 ≤ ⌊β⌋ + 1 - ⌊α⌋ := by omega
  have : ((⌊β⌋ + 1 - ⌊α⌋).toNat : ℝ) = ((⌊β⌋ + 1 - ⌊α⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [this]
  push_cast
  linarith

theorem card_dilateCells_le (c : ℝ) (w : ℤ × ℤ) :
    ((dilateCells c w).card : ℝ) ≤ (2 * |c| + 2) ^ 2 := by
  rw [dilateCells, Finset.card_product, Nat.cast_mul, sq]
  have hc := abs_nonneg c
  have h1 := card_Icc_floor_le (c * w.1 - |c|) (c * w.1 + |c|) (by linarith)
  have h2 := card_Icc_floor_le (c * w.2 - |c|) (c * w.2 + |c|) (by linarith)
  have e1 : c * w.1 + |c| - (c * w.1 - |c|) + 2 = 2 * |c| + 2 := by ring
  have e2 : c * w.2 + |c| - (c * w.2 - |c|) + 2 = 2 * |c| + 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem floor_mul_mem (c x : ℝ) :
    ⌊c * x⌋ ∈ Finset.Icc ⌊c * (⌊x⌋ : ℝ) - |c|⌋ ⌊c * (⌊x⌋ : ℝ) + |c|⌋ := by
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  have hd : |c * x - c * (⌊x⌋ : ℝ)| ≤ |c| := by
    rw [← mul_sub, abs_mul]
    have : |x - (⌊x⌋ : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    calc |c| * |x - (⌊x⌋ : ℝ)| ≤ |c| * 1 := by gcongr
      _ = |c| := mul_one _
  rw [abs_le] at hd
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_mono (by linarith), Int.floor_mono (by linarith)⟩

theorem cell_smul_mem (h c : ℝ) (x : ℝ × ℝ) : cell h (c • x) ∈ dilateCells c (cell h x) := by
  simp only [cell, dilateCells, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Finset.mem_product]
  constructor
  · rw [mul_div_assoc]; exact floor_mul_mem c (x.1 / h)
  · rw [mul_div_assoc]; exact floor_mul_mem c (x.2 / h)

theorem cells_smul_subset (h c : ℝ) (U : Finset (ℝ × ℝ)) :
    cells h (c • U) ⊆ (cells h U).biUnion (dilateCells c) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_cells.mp hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hy
  exact Finset.mem_biUnion.mpr ⟨cell h x, cell_mem_cells hx, cell_smul_mem h c x⟩

/-- Dilation by `c` multiplies the number of occupied cells by at most `(2|c| + 2)²`. -/
theorem card_cells_smul_le (h c : ℝ) (U : Finset (ℝ × ℝ)) :
    ((cells h (c • U)).card : ℝ) ≤ (2 * |c| + 2) ^ 2 * (cells h U).card := by
  calc ((cells h (c • U)).card : ℝ) ≤ ((cells h U).biUnion (dilateCells c)).card := by
        exact_mod_cast Finset.card_le_card (cells_smul_subset h c U)
    _ ≤ ∑ w ∈ cells h U, ((dilateCells c w).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ cells h U, (2 * |c| + 2) ^ 2 :=
        Finset.sum_le_sum fun w _ => card_dilateCells_le c w
    _ = (2 * |c| + 2) ^ 2 * (cells h U).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The reverse comparison for a nonzero dilation. -/
theorem card_cells_le_smul {h c : ℝ} (hc : c ≠ 0) (U : Finset (ℝ × ℝ)) :
    ((cells h U).card : ℝ) ≤ (2 * |c⁻¹| + 2) ^ 2 * (cells h (c • U)).card := by
  have := card_cells_smul_le h c⁻¹ (c • U)
  rwa [inv_smul_smul₀ hc] at this

theorem smul_sub_finset_subset (c : ℝ) (U V : Finset (ℝ × ℝ)) :
    c • U - c • V ⊆ c • (U - V) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.mp hb
  rw [← smul_sub]
  exact Finset.smul_mem_smul_finset (Finset.sub_mem_sub hx hy)

theorem smul_smul_finset (c d : ℝ) (U : Finset (ℝ × ℝ)) : c • d • U = (c * d) • U := by
  ext z
  simp only [Finset.mem_smul_finset]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by rw [smul_smul]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨d • x, ⟨x, hx, rfl⟩, by rw [smul_smul]⟩

end

end Submission.Obl.k4_retained_edge_planar_rigidity
