import Submission.Obl.k4_plank_projected_multiplicity.CellNeighborhood
import Submission.Obl.k4_plank_projected_multiplicity.Basic
import Submission.Obl.k4_scalar_coefficient_clustering.TimeBins

namespace Submission.Obl.k4_plank_projected_multiplicity

open Set Finset MeasureTheory
open Submission.Lib.K4PlankGeometry (binTime cellCode)
open Submission.Obl.k4_scalar_coefficient_clustering (timeCell)

noncomputable section

def localCellOffsets : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-5 : ℤ) 5)

theorem card_localCellOffsets : localCellOffsets.card = 121 := by
  norm_num [localCellOffsets, Fin.prod_univ_two]

theorem midpoint_trace_dist_le {D : ℕ} (hD : 1 ≤ D) (j : Fin D) {t : ℝ}
    (ht : t ∈ timeCell D j) (b u b' u' : E2) (hu : ‖u‖ ≤ 1) (hu' : ‖u'‖ ≤ 1)
    (hnear : ‖(b + t • u) - (b' + t • u')‖ ≤ 2 / (D : ℝ)) :
    ‖(b + binTime D j • u) - (b' + binTime D j • u')‖ ≤ 4 / (D : ℝ) := by
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have htime := Submission.Obl.k4_scalar_coefficient_clustering.timeCell_midpoint_dist hD j ht
  have hvelocity : ‖u - u'‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have heq : (b + binTime D j • u) - (b' + binTime D j • u') =
      ((b + t • u) - (b' + t • u')) + (binTime D j - t) • (u - u') := by module
  rw [heq]
  calc
    ‖((b + t • u) - (b' + t • u')) + (binTime D j - t) • (u - u')‖ ≤
        ‖(b + t • u) - (b' + t • u')‖ + ‖(binTime D j - t) • (u - u')‖ := norm_add_le _ _
    _ = ‖(b + t • u) - (b' + t • u')‖ + |binTime D j - t| * ‖u - u'‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 / (D : ℝ) + (1 / (D : ℝ)) * 2 :=
      add_le_add hnear (mul_le_mul htime hvelocity (norm_nonneg _) (by positivity))
    _ = 4 / (D : ℝ) := by ring

/-- Two traces meeting at a time in the same cell have neighboring midpoint codes. -/
theorem cellCode_near_of_timeCell {D : ℕ} (hD : 1 ≤ D) (j : Fin D) {t : ℝ}
    (ht : t ∈ timeCell D j) (b u b' u' : E2) (hu : ‖u‖ ≤ 1) (hu' : ‖u'‖ ≤ 1)
    (hnear : ‖(b + t • u) - (b' + t • u')‖ ≤ 2 / (D : ℝ)) :
    cellCode D b u j ∈ expandProjectedCells {cellCode D b' u' j} localCellOffsets := by
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hmid := midpoint_trace_dist_le hD j ht b u b' u' hu hu' hnear
  let r : Fin 2 → ℤ := fun k =>
    ⌊(D : ℝ) * (b + binTime D j • u) k⌋ - ⌊(D : ℝ) * (b' + binTime D j • u') k⌋
  have hr : r ∈ localCellOffsets := by
    apply Fintype.mem_piFinset.mpr
    intro k
    have hcoord := (PiLp.norm_apply_le
      ((b + binTime D j • u) - (b' + binTime D j • u')) k).trans hmid
    change |(b + binTime D j • u) k - (b' + binTime D j • u') k| ≤ 4 / (D : ℝ) at hcoord
    have hscaled : |(D : ℝ) * (b + binTime D j • u) k -
        (D : ℝ) * (b' + binTime D j • u') k| ≤ 4 := by
      rw [← mul_sub, abs_mul, abs_of_pos hDp]
      calc
        (D : ℝ) * |(b + binTime D j • u) k - (b' + binTime D j • u') k| ≤
            (D : ℝ) * (4 / (D : ℝ)) := mul_le_mul_of_nonneg_left hcoord hDp.le
        _ = 4 := by field_simp
    have hfloor : |(⌊(D : ℝ) * (b + binTime D j • u) k⌋ : ℝ) -
        ⌊(D : ℝ) * (b' + binTime D j • u') k⌋| ≤ 5 := by
      have h₁ := Int.floor_le ((D : ℝ) * (b + binTime D j • u) k)
      have h₂ := Int.floor_le ((D : ℝ) * (b' + binTime D j • u') k)
      have h₃ := Int.lt_floor_add_one ((D : ℝ) * (b + binTime D j • u) k)
      have h₄ := Int.lt_floor_add_one ((D : ℝ) * (b' + binTime D j • u') k)
      have hh := abs_le.mp hscaled
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    apply Finset.mem_Icc.mpr
    dsimp [r]
    exact_mod_cast abs_le.mp hfloor
  apply Finset.mem_image.mpr
  refine ⟨(cellCode D b' u' j, r), Finset.mem_product.mpr ⟨by simp, hr⟩, ?_⟩
  apply Prod.ext
  · rfl
  · funext k
    dsimp [cellCode, r]
    omega

/-- Any set covered by selected time cells has the corresponding marked-time bound. -/
theorem volume_le_selected_time_cells {D : ℕ} (hD : 1 ≤ D) (J : Finset (Fin D))
    (E : Set ℝ) (hE : ∀ t ∈ E, ∃ j ∈ J, t ∈ timeCell D j) :
    volume E ≤ ENNReal.ofReal ((J.card : ℝ) / (D : ℝ)) := by
  have hDp : 0 < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hsub : E ⊆ ⋃ j ∈ J, timeCell D j := by
    intro t ht
    obtain ⟨j, hj, htj⟩ := hE t ht
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, htj⟩⟩
  calc
    volume E ≤ volume (⋃ j ∈ J, timeCell D j) := measure_mono hsub
    _ ≤ ∑ j ∈ J, volume (timeCell D j) := measure_biUnion_finset_le _ _
    _ = ∑ _j ∈ J, ENNReal.ofReal (1 / (D : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [timeCell, Real.volume_Icc]
      congr 1
      ring
    _ = ENNReal.ofReal ((J.card : ℝ) / (D : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

end

end Submission.Obl.k4_plank_projected_multiplicity
