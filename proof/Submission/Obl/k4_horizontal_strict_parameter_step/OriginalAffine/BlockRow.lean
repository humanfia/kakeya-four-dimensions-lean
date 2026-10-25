/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 89648dfeac59b903d3d93ae0dca8d07a6202ebdf, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/BlockRow.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.BlockNumerics
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open Set MeasureTheory

/-- Assemble one selected row per original closed time block.  The sum is zero
off the blocks, and agrees with the selected row wherever the block is unique. -/
noncomputable def closedBlockRow {H : ℕ} (row : Fin H → ℝ → Fin 2 → ℝ)
    (t : ℝ) (e : Fin 2) : ℝ :=
  ∑ j : Fin H, (Icc ((j : ℝ) / H) (((j : ℝ) + 1) / H)).indicator
    (fun u => row j u e) t

theorem measurable_closedBlockRow {H : ℕ} (row : Fin H → ℝ → Fin 2 → ℝ)
    (hrow : ∀ j, Measurable (row j)) : Measurable (closedBlockRow row) := by
  apply Measurable.of_eval
  intro e
  exact Finset.measurable_sum _ (fun j _ =>
    ((measurable_pi_apply e).comp (hrow j)).indicator measurableSet_Icc)

/-- Endpoints pay at most a factor two.  No count of the full time partition
appears in the uniform row bound. -/
theorem closedBlockRow_bound {H : ℕ} (hH : 0 < H)
    (row : Fin H → ℝ → Fin 2 → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ (j : Fin H) (t : ℝ), t ∈ Icc ((j : ℝ) / H) (((j : ℝ) + 1) / H) →
      ∀ e, |row j t e| ≤ M) (t : ℝ) (e : Fin 2) :
    |closedBlockRow row t e| ≤ 2 * M := by
  classical
  let S : Finset (Fin H) := Finset.univ.filter fun j =>
    t ∈ Icc ((j : ℝ) / H) (((j : ℝ) + 1) / H)
  have hcard : S.card ≤ 2 := closed_grid_blocks_card hH S t
    (fun j hj => (Finset.mem_filter.mp hj).2)
  have heq : closedBlockRow row t e = ∑ j ∈ S, row j t e := by
    simp only [closedBlockRow, S, Finset.sum_filter, Set.indicator_apply]
  rw [heq]
  calc
    _ ≤ ∑ j ∈ S, |row j t e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ S, M := Finset.sum_le_sum (fun j hj =>
      hrow j t (Finset.mem_filter.mp hj).2 e)
    _ = (S.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM

/-- On the pointwise unique-block discovery set, the assembled row is exactly
the chosen native row, including at every retained endpoint time. -/
theorem closedBlockRow_eq {H : ℕ} (row : Fin H → ℝ → Fin 2 → ℝ)
    (t : ℝ) (j₀ : Fin H)
    (ht : t ∈ Icc ((j₀ : ℝ) / H) (((j₀ : ℝ) + 1) / H))
    (hunique : ∀ j : Fin H,
      t ∈ Icc ((j : ℝ) / H) (((j : ℝ) + 1) / H) → j = j₀) :
    closedBlockRow row t = row j₀ t := by
  classical
  funext e
  unfold closedBlockRow
  rw [Finset.sum_eq_single j₀]
  · exact Set.indicator_of_mem ht _
  · intro j _ hne
    exact Set.indicator_of_notMem (fun hj => hne (hunique j hj)) _
  · intro h
    exact False.elim (h (Finset.mem_univ j₀))

end Submission.Obl.k4_horizontal_strict_parameter_step
