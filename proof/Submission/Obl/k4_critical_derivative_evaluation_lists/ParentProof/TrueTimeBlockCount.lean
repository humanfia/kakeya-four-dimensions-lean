/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, TrueTimeBlockCount.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_finite_row_graph_assembly.Projection
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking
/-! Adapted from this LOT tree, obligation o107, session x0353,
`Submission/Obl/k4_finite_narrowness_path_improvement/TrueTimeBlockCount.lean`
(commit 2d33b59a). -/


/-! Only boundedly many true time blocks can meet one finer scalar time bin.
Closed true-block endpoints are allowed throughout. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Finset
open scoped Classical

theorem true_time_blocks_in_fine_bin
    {I : Type*} (S : Finset I) (block : I → ℤ) (time : I → ℝ)
    (H a : ℝ) (n : ℤ) (hH : 0 < H) (ha : 0 < a) (haH : a ≤ H)
    (htrue : ∀ i ∈ S, (block i : ℝ) * H ≤ time i ∧ time i ≤ ((block i : ℝ) + 1) * H)
    (hfine : ∀ i ∈ S, ⌊time i / a⌋ = n) :
    ((S.image block).card : ℝ) ≤ 6 := by
  apply (Submission.Obl.k4_scalar_coefficient_clustering.card_int_grid_of_diameter
    (S.image block) (L := 2) (by norm_num) ?_).trans_eq (by norm_num)
  intro k hk l hl
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
  have hgap := Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq
    ha ((hfine i hi).trans (hfine j hj).symm)
  have hup : (block i : ℝ) - (block j : ℝ) ≤ 2 := by
    apply (mul_le_mul_iff_left₀ hH).mp
    nlinarith only [(htrue i hi).1, (htrue j hj).2, (abs_le.mp hgap).2, haH]
  have hdown : -(2 : ℝ) ≤ (block i : ℝ) - (block j : ℝ) := by
    apply (mul_le_mul_iff_left₀ hH).mp
    nlinarith only [(htrue i hi).2, (htrue j hj).1, (abs_le.mp hgap).1, haH]
  exact abs_le.mpr ⟨hdown, hup⟩

/-- Contacted labels may be counted on each old true block, then combined in
a fine scalar time bin at only an absolute cost. -/
theorem true_labels_across_fine_time_bin
    {I : Type*} (S : Finset I) (block : I → ℤ) (time : I → ℝ)
    (H a B : ℝ) (n : ℤ) (hH : 0 < H) (ha : 0 < a) (haH : a ≤ H) (hB : 0 ≤ B)
    (htrue : ∀ i ∈ S, (block i : ℝ) * H ≤ time i ∧ time i ≤ ((block i : ℝ) + 1) * H)
    (hfine : ∀ i ∈ S, ⌊time i / a⌋ = n)
    (hcount : ∀ k, ((S.filter (fun i => block i = k)).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ 6 * B := by
  have hblocks := true_time_blocks_in_fine_bin S block time H a n hH ha haH htrue hfine
  calc
    _ = ∑ k ∈ S.image block, ((S.filter (fun i => block i = k)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (s := S) (t := S.image block) (f := block)
        (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    _ ≤ ∑ _k ∈ S.image block, B := Finset.sum_le_sum (fun k _ => hcount k)
    _ = ((S.image block).card : ℝ) * B := by simp
    _ ≤ 6 * B := mul_le_mul_of_nonneg_right hblocks hB

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
