-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceGeometry.CurveCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceGeometry/CurveCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceGeometry/CurveCells.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceGeometry/CurveCells.lean.
-- Existing source attributions are preserved below.

/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o106,
   session x0352, commit b976e86c1df62f72f3fa9d42b0a0c928d33ecc7d;
   original file Submission/Obl/k4_isotropic_path_improvement/CurveCells.lean.
   Existing source comments and attributions are preserved below. -/
import Submission.Lib.K4IncidenceWitnesses
import Submission.Obl.k4_matching_homogeneous_records.Offsets

/-!
A coordinate-Lipschitz trajectory visits only O(1/q) cubes of width q.
The estimate is independent of the position of the trajectory and is
suitable for summed retained-duration deletion over physical cubes.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

open Set
open Submission.Lib.K4IncidenceWitnesses

noncomputable section

/-- A finite set of occupied spatial cells, with one actual time witness for
each cell, has a uniform trajectory count. -/
theorem trajectory_cell_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → ι → ℝ) (C : Finset (ι → ℤ)) (t : (ι → ℤ) → ℝ)
    (H q : ℝ) (hH : 0 ≤ H) (hq : 0 < q)
    (hcoord : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ j,
      |F s j - F t j| ≤ H * |s - t|)
    (ht : ∀ c ∈ C, t c ∈ Icc (0 : ℝ) 1)
    (hcode : ∀ c ∈ C, ∀ j, ⌊F (t c) j / q⌋ = c j) :
    (C.card : ℝ) ≤ (2 / q + 3) * (2 * H + 5) ^ Fintype.card ι := by
  classical
  let code (c : ι → ℤ) : Fin 1 → ℤ := fun _ => ⌊t c / q⌋
  let J := C.image code
  have hfloor (c : ι → ℤ) (hc : c ∈ C) :
      0 ≤ (⌊t c / q⌋ : ℝ) ∧ (⌊t c / q⌋ : ℝ) ≤ 1 / q := by
    have hlo : (0 : ℤ) ≤ ⌊t c / q⌋ := Int.floor_nonneg.mpr (by positivity [(ht c hc).1])
    refine ⟨by exact_mod_cast hlo, (Int.floor_le _).trans ?_⟩
    exact div_le_div_of_nonneg_right (ht c hc).2 hq.le
  have hJcard : (J.card : ℝ) ≤ 2 / q + 3 := by
    have hdiam : ∀ i ∈ J, ∀ i' ∈ J, ∀ j, |(i j : ℝ) - (i' j : ℝ)| ≤ 1 / q := by
      intro i hi i' hi' j
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hi'
      exact abs_le.mpr ⟨by dsimp [code]; linarith [(hfloor c hc).1, (hfloor c' hc').2],
        by dsimp [code]; linarith [(hfloor c hc).2, (hfloor c' hc').1]⟩
    simpa only [Fintype.card_fin, pow_one, mul_one_div] using
      card_pi_grid_of_diameter J (show 0 ≤ 1 / q by positivity) hdiam
  have hfiber (i : Fin 1 → ℤ) :
      ((C.filter fun c => code c = i).card : ℝ) ≤ (2 * H + 5) ^ Fintype.card ι := by
    have hdiam : ∀ c ∈ C.filter (fun c => code c = i),
        ∀ c' ∈ C.filter (fun c => code c = i), ∀ j,
        |(c j : ℝ) - (c' j : ℝ)| ≤ H + 1 := by
      intro c hc c' hc' j
      obtain ⟨hc, hci⟩ := Finset.mem_filter.mp hc
      obtain ⟨hc', hc'i⟩ := Finset.mem_filter.mp hc'
      have hsame : ⌊t c / q⌋ = ⌊t c' / q⌋ := congrFun (hci.trans hc'i.symm) 0
      have hdt : |t c - t c'| ≤ q := by
        have h := (Int.abs_sub_lt_one_of_floor_eq_floor hsame).le
        rw [← sub_div, abs_div, abs_of_pos hq, div_le_iff₀ hq] at h
        simpa only [one_mul] using h
      have hF : |F (t c) j - F (t c') j| ≤ H * q :=
        (hcoord (t c) (ht c hc) (t c') (ht c' hc') j).trans
          (mul_le_mul_of_nonneg_left hdt hH)
      have hscaled : |F (t c) j / q - F (t c') j / q| ≤ H := by
        rw [← sub_div, abs_div, abs_of_pos hq, div_le_iff₀ hq]
        exact hF
      have h := Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound
        (F (t c) j / q) (F (t c') j / q)
      rw [hcode c hc j, hcode c' hc' j, Int.cast_sub] at h
      linarith
    have h := card_pi_grid_of_diameter (C.filter fun c => code c = i)
      (show 0 ≤ H + 1 by linarith) hdiam
    convert h using 1
    congr 1
    ring
  have htotal : (C.card : ℝ) ≤ (J.card : ℝ) * (2 * H + 5) ^ Fintype.card ι := by
    rw [Finset.card_eq_sum_card_image code C, Nat.cast_sum]
    exact (Finset.sum_le_sum fun i _ => hfiber i).trans_eq (by simp [J])
  exact htotal.trans (mul_le_mul_of_nonneg_right hJcard (by positivity))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
