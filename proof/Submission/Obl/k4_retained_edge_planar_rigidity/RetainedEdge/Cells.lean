-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/Cells.lean;
-- only the namespace and module paths were renamed to o071's.
import Mathlib

/-!
# Grid cells of finite planar sets

Paper Section 7 (`sec:retained-edge-tools`) measures planar sets by their covering number `N_h` by
squares of side `h`. For a finite set `U ⊆ ℝ × ℝ` we use the set of grid cells
`cells h U = {(⌊x₁/h⌋, ⌊x₂/h⌋) : x ∈ U} ⊆ ℤ × ℤ`; its cardinality is `N_h(U)` up to a fixed factor.
Sums, differences, negation and dilation of real sets change cell sets by bounded error boxes, which
is what lets the Ruzsa calculus of `ℤ × ℤ` transfer to real sets (file `CellRuzsa`).
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

/-- The cell of mesh `h` containing a planar point. -/
def cell (h : ℝ) (x : ℝ × ℝ) : ℤ × ℤ := (⌊x.1 / h⌋, ⌊x.2 / h⌋)

/-- The cells of mesh `h` met by a finite planar set. -/
def cells (h : ℝ) (U : Finset (ℝ × ℝ)) : Finset (ℤ × ℤ) := U.image (cell h)

/-- The square error box `[a, b]²` of integer offsets. -/
def ebox (a b : ℤ) : Finset (ℤ × ℤ) := Finset.Icc a b ×ˢ Finset.Icc a b

theorem card_ebox (a b : ℤ) : (ebox a b).card = ((b + 1 - a).toNat) ^ 2 := by
  simp [ebox, Finset.card_product, Int.card_Icc, sq]

theorem card_ebox01 : (ebox 0 1).card = 4 := by
  rw [card_ebox]; rfl

theorem card_eboxm10 : (ebox (-1) 0).card = 4 := by
  rw [card_ebox]; rfl

theorem mem_cells {h : ℝ} {U : Finset (ℝ × ℝ)} {z : ℤ × ℤ} :
    z ∈ cells h U ↔ ∃ x ∈ U, cell h x = z := by
  simp [cells]

theorem cell_mem_cells {h : ℝ} {U : Finset (ℝ × ℝ)} {x : ℝ × ℝ} (hx : x ∈ U) :
    cell h x ∈ cells h U :=
  Finset.mem_image_of_mem _ hx

theorem card_cells_le (h : ℝ) (U : Finset (ℝ × ℝ)) : (cells h U).card ≤ U.card :=
  Finset.card_image_le

theorem cells_mono {h : ℝ} {U V : Finset (ℝ × ℝ)} (hUV : U ⊆ V) : cells h U ⊆ cells h V :=
  Finset.image_subset_image hUV

theorem cells_nonempty {h : ℝ} {U : Finset (ℝ × ℝ)} (hU : U.Nonempty) : (cells h U).Nonempty :=
  hU.image _

/-! ### Floors of sums and differences -/

theorem floor_add_sub_mem (a b : ℝ) : ⌊a + b⌋ - (⌊a⌋ + ⌊b⌋) ∈ Finset.Icc (0 : ℤ) 1 := by
  have h1 := Int.le_floor_add a b
  have h2 := Int.le_floor_add_floor a b
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem floor_sub_sub_mem (a b : ℝ) : ⌊a - b⌋ - (⌊a⌋ - ⌊b⌋) ∈ Finset.Icc (-1 : ℤ) 0 := by
  have ha := Int.floor_le a
  have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  have h1 : ((⌊a⌋ - ⌊b⌋ - 1 : ℤ) : ℝ) ≤ a - b := by push_cast; linarith
  have h2 : a - b < ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) + 1 := by push_cast; linarith
  have e1 : ⌊a⌋ - ⌊b⌋ - 1 ≤ ⌊a - b⌋ := Int.le_floor.mpr h1
  have e2 : ⌊a - b⌋ < ⌊a⌋ - ⌊b⌋ + 1 := Int.floor_lt.mpr (by push_cast at h2 ⊢; linarith)
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem floor_neg_add_mem (a : ℝ) : ⌊-a⌋ + ⌊a⌋ ∈ Finset.Icc (-1 : ℤ) 0 := by
  rw [Int.floor_neg]
  have h1 := Int.floor_le_ceil a
  have h2 := Int.ceil_le_floor_add_one a
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem cell_add_sub_mem (h : ℝ) (x y : ℝ × ℝ) :
    cell h (x + y) - (cell h x + cell h y) ∈ ebox 0 1 := by
  simp only [cell, ebox, Prod.fst_add, Prod.snd_add, add_div, Prod.mk_add_mk, Prod.mk_sub_mk,
    Finset.mem_product]
  exact ⟨floor_add_sub_mem _ _, floor_add_sub_mem _ _⟩

theorem cell_sub_sub_mem (h : ℝ) (x y : ℝ × ℝ) :
    cell h (x - y) - (cell h x - cell h y) ∈ ebox (-1) 0 := by
  simp only [cell, ebox, Prod.fst_sub, Prod.snd_sub, sub_div, Prod.mk_sub_mk, Finset.mem_product]
  exact ⟨floor_sub_sub_mem _ _, floor_sub_sub_mem _ _⟩

theorem cell_neg_add_mem (h : ℝ) (x : ℝ × ℝ) : cell h (-x) + cell h x ∈ ebox (-1) 0 := by
  simp only [cell, ebox, Prod.fst_neg, Prod.snd_neg, neg_div, Prod.mk_add_mk, Finset.mem_product]
  exact ⟨floor_neg_add_mem _, floor_neg_add_mem _⟩

/-! ### Cell sets of sums, differences and negatives -/

theorem cells_add_subset (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    cells h (U + V) ⊆ cells h U + cells h V + ebox 0 1 := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_cells.mp hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hw
  refine Finset.mem_add.mpr ⟨cell h x + cell h y, Finset.add_mem_add (cell_mem_cells hx)
    (cell_mem_cells hy), _, cell_add_sub_mem h x y, ?_⟩
  abel

theorem add_cells_subset (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    cells h U + cells h V ⊆ cells h (U + V) - ebox 0 1 := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨x, hx, rfl⟩ := mem_cells.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_cells.mp hb
  refine Finset.mem_sub.mpr ⟨cell h (x + y), cell_mem_cells (Finset.add_mem_add hx hy), _,
    cell_add_sub_mem h x y, ?_⟩
  abel

theorem cells_sub_subset (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    cells h (U - V) ⊆ cells h U - cells h V + ebox (-1) 0 := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_cells.mp hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hw
  refine Finset.mem_add.mpr ⟨cell h x - cell h y, Finset.sub_mem_sub (cell_mem_cells hx)
    (cell_mem_cells hy), _, cell_sub_sub_mem h x y, ?_⟩
  abel

theorem sub_cells_subset (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    cells h U - cells h V ⊆ cells h (U - V) - ebox (-1) 0 := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨x, hx, rfl⟩ := mem_cells.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_cells.mp hb
  refine Finset.mem_sub.mpr ⟨cell h (x - y), cell_mem_cells (Finset.sub_mem_sub hx hy), _,
    cell_sub_sub_mem h x y, ?_⟩
  abel

theorem cells_neg_subset (h : ℝ) (U : Finset (ℝ × ℝ)) :
    cells h (-U) ⊆ ebox (-1) 0 - cells h U := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_cells.mp hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_neg.mp hw
  refine Finset.mem_sub.mpr ⟨_, cell_neg_add_mem h x, cell h x, cell_mem_cells hx, ?_⟩
  simp

theorem card_cells_add_le (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    (cells h (U + V)).card ≤ (cells h U + cells h V).card * 4 := by
  calc (cells h (U + V)).card ≤ (cells h U + cells h V + ebox 0 1).card :=
        Finset.card_le_card (cells_add_subset h U V)
    _ ≤ (cells h U + cells h V).card * (ebox 0 1).card := Finset.card_add_le
    _ = (cells h U + cells h V).card * 4 := by rw [card_ebox01]

theorem card_add_cells_le (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    (cells h U + cells h V).card ≤ (cells h (U + V)).card * 4 := by
  calc (cells h U + cells h V).card ≤ (cells h (U + V) - ebox 0 1).card :=
        Finset.card_le_card (add_cells_subset h U V)
    _ ≤ (cells h (U + V)).card * (ebox 0 1).card := Finset.card_sub_le
    _ = (cells h (U + V)).card * 4 := by rw [card_ebox01]

theorem card_cells_sub_le (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    (cells h (U - V)).card ≤ (cells h U - cells h V).card * 4 := by
  calc (cells h (U - V)).card ≤ (cells h U - cells h V + ebox (-1) 0).card :=
        Finset.card_le_card (cells_sub_subset h U V)
    _ ≤ (cells h U - cells h V).card * (ebox (-1) 0).card := Finset.card_add_le
    _ = (cells h U - cells h V).card * 4 := by
        rw [card_eboxm10]

theorem card_sub_cells_le (h : ℝ) (U V : Finset (ℝ × ℝ)) :
    (cells h U - cells h V).card ≤ (cells h (U - V)).card * 4 := by
  calc (cells h U - cells h V).card ≤ (cells h (U - V) - ebox (-1) 0).card :=
        Finset.card_le_card (sub_cells_subset h U V)
    _ ≤ (cells h (U - V)).card * (ebox (-1) 0).card := Finset.card_sub_le
    _ = (cells h (U - V)).card * 4 := by
        rw [card_eboxm10]

theorem card_cells_neg_le (h : ℝ) (U : Finset (ℝ × ℝ)) :
    (cells h (-U)).card ≤ (cells h U).card * 4 := by
  calc (cells h (-U)).card ≤ (ebox (-1) 0 - cells h U).card :=
        Finset.card_le_card (cells_neg_subset h U)
    _ ≤ (ebox (-1) 0).card * (cells h U).card := Finset.card_sub_le
    _ = (cells h U).card * 4 := by
        rw [card_eboxm10, mul_comm]

end

end Submission.Obl.k4_retained_edge_planar_rigidity
