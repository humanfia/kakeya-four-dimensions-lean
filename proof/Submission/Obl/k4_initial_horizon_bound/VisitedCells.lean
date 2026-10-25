import Submission.Obl.k4_initial_horizon_bound.TimeMarks
import Submission.Obl.k4_plank_projected_multiplicity.TimeCells

/-! Transfer old actual-time cells to the midpoint table in the plank input. -/

open MeasureTheory Set

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Lib.K4PlankGeometry (cellCode)
open Submission.Obl.k4_plank_projected_multiplicity
  (expandProjectedCells localCellOffsets cellCode_near_of_timeCell
    card_expandProjectedCells card_localCellOffsets)

noncomputable def actualBaseCell {α : Type*} (D : ℕ)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (p : α × ℝ) : ℕ × (Fin 2 → ℤ) :=
  (⌊(D : ℝ) * p.2⌋₊, fun i => ⌊(D : ℝ) * (b p.1 + p.2 • u p.1) i⌋)

theorem measurable_actualBaseCell {α : Type*} [MeasurableSpace α] (D : ℕ)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (hb : Measurable b) (hu : Measurable u) :
    Measurable (actualBaseCell D b u) := by
  unfold actualBaseCell
  apply Measurable.prodMk
  · exact Nat.measurable_floor.comp (measurable_const.mul measurable_snd)
  · apply Measurable.of_eval
    intro i
    apply Int.measurable_floor.comp
    fun_prop

theorem floor_time_eq_of_interior {D : ℕ} (hD : 1 ≤ D) (j : Fin D) {t : ℝ}
    (ht : t ∈ Ioo (((j : ℕ) : ℝ) / D) ((((j : ℕ) : ℝ) + 1) / D)) :
    ⌊(D : ℝ) * t⌋₊ = (j : ℕ) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlo : ((j : ℕ) : ℝ) < (D : ℝ) * t := by
    simpa only [mul_comm] using (div_lt_iff₀ hDp).mp ht.1
  have hhi : (D : ℝ) * t < ((j : ℕ) : ℝ) + 1 := by
    simpa only [mul_comm] using (lt_div_iff₀ hDp).mp ht.2
  have hnonneg : 0 ≤ (D : ℝ) * t := (Nat.cast_nonneg (j : ℕ)).trans hlo.le
  exact (Nat.floor_eq_iff hnonneg).mpr ⟨hlo.le, hhi⟩

/-- A positive-duration mark has an interior witness in an old actual-time
cell. The accepted fixed neighbor expansion therefore covers its midpoint. -/
theorem positiveTimeMarks_visited_table_at {α : Type*} {D : ℕ} (hD : 1 ≤ D)
    (b u : α → EuclideanSpace ℝ (Fin 2))
    (E : Set (α × ℝ)) (F : Finset (ℕ × (Fin 2 → ℤ)))
    (hF : ∀ p ∈ E, actualBaseCell D b u p ∈ F) (x : α) (hu : ‖u x‖ ≤ 1) (j : Fin D)
    (hj : j ∈ positiveTimeMarks D E x) :
    cellCode D (b x) (u x) j ∈ expandProjectedCells F localCellOffsets := by
  classical
  obtain ⟨t, htE, ht⟩ := positiveTimeMarks_witness_interior hj
  let z := b x + t • u x
  have heq : cellCode D z 0 j = actualBaseCell D b u (x, t) := by
    apply Prod.ext
    · exact (floor_time_eq_of_interior hD j ht).symm
    · simp only [cellCode, smul_zero, add_zero, actualBaseCell, z]
  have hnear : ‖(b x + t • u x) - (z + t • (0 : EuclideanSpace ℝ (Fin 2)))‖ ≤
      2 / (D : ℝ) := by simp only [z, smul_zero, add_zero, sub_self, norm_zero]; positivity
  have hcode := cellCode_near_of_timeCell hD j ⟨ht.1.le, ht.2.le⟩
    (b x) (u x) z 0 hu (by simp) hnear
  rw [heq] at hcode
  obtain ⟨⟨p, r⟩, hpr, hcode⟩ := Finset.mem_image.mp hcode
  obtain ⟨hp, hr⟩ := Finset.mem_product.mp hpr
  obtain rfl := Finset.mem_singleton.mp hp
  exact Finset.mem_image.mpr ⟨(actualBaseCell D b u (x, t), r),
    Finset.mem_product.mpr ⟨hF (x, t) htE, hr⟩, hcode⟩

theorem positiveTimeMarks_visited_table {α : Type*} {D : ℕ} (hD : 1 ≤ D)
    (b u : α → EuclideanSpace ℝ (Fin 2)) (hu : ∀ x, ‖u x‖ ≤ 1)
    (E : Set (α × ℝ)) (F : Finset (ℕ × (Fin 2 → ℤ)))
    (hF : ∀ p ∈ E, actualBaseCell D b u p ∈ F) (x : α) (j : Fin D)
    (hj : j ∈ positiveTimeMarks D E x) :
    cellCode D (b x) (u x) j ∈ expandProjectedCells F localCellOffsets :=
  positiveTimeMarks_visited_table_at hD b u E F hF x (hu x) j hj

theorem expanded_visited_table_card (F : Finset (ℕ × (Fin 2 → ℤ))) :
    (expandProjectedCells F localCellOffsets).card ≤ 121 * F.card := by
  simpa only [card_localCellOffsets, Nat.mul_comm] using
    card_expandProjectedCells F localCellOffsets

end Submission.Obl.k4_initial_horizon_bound
