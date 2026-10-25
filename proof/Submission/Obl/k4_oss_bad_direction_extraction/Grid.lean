import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Submission.Obl.k4_oss_bad_direction_extraction

noncomputable section

private abbrev C := Submission.Obl.k4_oss_collision_cauchy_schwarz.cell

/-- The cells meeting the unit interval, including its right endpoint. -/
def gridSize (δ : ℝ) : ℕ := ⌊δ⁻¹⌋₊ + 1

def gridCell (δ : ℝ) (i : Fin (gridSize δ)) : Set ℝ := C δ (i : ℕ)

theorem measurableSet_gridCell {δ : ℝ} (i : Fin (gridSize δ)) :
    MeasurableSet (gridCell δ i) :=
  Submission.Obl.k4_oss_collision_cauchy_schwarz.measurableSet_cell _ _

theorem gridCell_disjoint (δ : ℝ) :
    Pairwise (fun i j : Fin (gridSize δ) => Disjoint (gridCell δ i) (gridCell δ j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have he : (i : ℕ) = (j : ℕ) := by
    exact_mod_cast (hx.symm.trans hy : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ))
  exact hij (Fin.ext he)

theorem gridCell_dist_le {δ : ℝ} (hδ : 0 < δ) {i : Fin (gridSize δ)}
    {x y : ℝ} (hx : x ∈ gridCell δ i) (hy : y ∈ gridCell δ i) : dist x y ≤ δ := by
  rw [Real.dist_eq]
  exact Submission.Obl.k4_oss_collision_cauchy_schwarz.abs_sub_le_of_same_cell hδ
    (hx.trans hy.symm)

theorem grid_cover {δ : ℝ} (hδ : 0 < δ) :
    Icc (0 : ℝ) 1 ⊆ ⋃ i : Fin (gridSize δ), gridCell δ i := by
  intro x hx
  have hx0 : 0 ≤ x / δ := div_nonneg hx.1 hδ.le
  have hx1 : x / δ ≤ δ⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hx.2 hδ.le
  let i : Fin (gridSize δ) :=
    ⟨⌊x / δ⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hx1)⟩
  refine mem_iUnion.mpr ⟨i, ?_⟩
  exact (Int.natCast_floor_eq_floor hx0).symm

theorem gridSize_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (gridSize δ : ℝ) ≤ 2 * δ⁻¹ := by
  have h1 : 1 ≤ δ⁻¹ := by
    rw [← one_div, le_div_iff₀ hδ]
    simpa using hδ1
  have hf := Nat.floor_le (inv_nonneg.mpr hδ.le)
  simp only [gridSize, Nat.cast_add, Nat.cast_one]
  linarith

theorem sum_grid_mass (μ : Measure ℝ) [IsFiniteMeasure μ] {δ : ℝ} (hδ : 0 < δ)
    {E : Set ℝ} (hE : MeasurableSet E) (hsupp : E ⊆ Icc (0 : ℝ) 1) :
    ∑ i : Fin (gridSize δ), μ.real (E ∩ gridCell δ i) = μ.real E := by
  have hd : Pairwise (fun i j : Fin (gridSize δ) =>
      Disjoint (E ∩ gridCell δ i) (E ∩ gridCell δ j)) := by
    intro i j hij
    exact (gridCell_disjoint δ hij).mono inter_subset_right inter_subset_right
  rw [← measureReal_iUnion_fintype hd (fun i => hE.inter (measurableSet_gridCell i))]
  congr 1
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨_, hx, _⟩ => hx,
    fun hx => (mem_iUnion.mp (grid_cover hδ (hsupp hx))).imp (fun _ hi => ⟨hx, hi⟩)⟩

end
end Submission.Obl.k4_oss_bad_direction_extraction
