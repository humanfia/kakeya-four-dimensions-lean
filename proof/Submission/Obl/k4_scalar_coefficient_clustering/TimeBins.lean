import Submission.Obl.k4_scalar_coefficient_clustering.Bins
import Submission.Lib.K4PlankGeometry

namespace Submission.Obl.k4_scalar_coefficient_clustering

open MeasureTheory Set
open Submission.Lib.K4PlankGeometry (binTime)

noncomputable section

def timeCell (D : ℕ) (j : Fin D) : Set ℝ :=
  Set.Icc (((j : ℕ) : ℝ) / (D : ℝ)) ((((j : ℕ) : ℝ) + 1) / (D : ℝ))

theorem exists_timeCell {D : ℕ} (hD : 1 ≤ D) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : Fin D, t ∈ timeCell D j := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  by_cases ht1 : t = 1
  · refine ⟨⟨D - 1, by omega⟩, ?_⟩
    have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
      rw [Nat.cast_sub hD, Nat.cast_one]
    simp only [timeCell, ht1, Set.mem_Icc, hcast]
    constructor
    · apply (div_le_iff₀ hDpos).mpr
      linarith
    · simp [hDpos.ne']
  · have hlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    have hf : ⌊(D : ℝ) * t⌋₊ < D :=
      (Nat.floor_lt (mul_nonneg hDpos.le ht.1)).mpr (by nlinarith)
    refine ⟨⟨⌊(D : ℝ) * t⌋₊, hf⟩, ?_⟩
    change ((⌊(D : ℝ) * t⌋₊ : ℝ) / (D : ℝ) ≤ t) ∧
      t ≤ ((⌊(D : ℝ) * t⌋₊ : ℝ) + 1) / (D : ℝ)
    constructor
    · exact (div_le_iff₀ hDpos).mpr (by
        simpa only [mul_comm] using Nat.floor_le (mul_nonneg hDpos.le ht.1))
    · exact (le_div_iff₀ hDpos).mpr (by
        have hh := (Nat.lt_floor_add_one ((D : ℝ) * t)).le
        simpa only [mul_comm] using hh)

theorem timeCell_midpoint_dist {D : ℕ} (hD : 1 ≤ D) (j : Fin D)
    {t : ℝ} (ht : t ∈ timeCell D j) : |binTime D j - t| ≤ 1 / (D : ℝ) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlo := (div_le_iff₀ hDpos).mp ht.1
  have hhi := (le_div_iff₀ hDpos).mp ht.2
  have heq : binTime D j - t = ((((j : ℕ) : ℝ) + 1 / 2) - t * (D : ℝ)) / (D : ℝ) := by
    dsimp [binTime]
    field_simp
  rw [heq, abs_div, abs_of_pos hDpos, div_le_div_iff_of_pos_right hDpos, abs_le]
  constructor <;> linarith

def labeledTimeMarks {α : Type*} (D : ℕ) (a : α → Coeff) (G : Set α)
    (E : Set (α × ℝ)) (p : ℝ) (q : Fin 3 → ℤ) : Finset (Fin D) := by
  classical
  exact Finset.univ.filter (fun j => ∃ l ∈ G, coefficientCode p (a l) = q ∧
    ∃ t, (l, t) ∈ E ∧ t ∈ timeCell D j)

theorem volume_fiber_le_marks {α : Type*} {D : ℕ} (hD : 1 ≤ D)
    (a : α → Coeff) (G : Set α) (E : Set (α × ℝ)) (p : ℝ)
    (hunit : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) {l : α} (hl : l ∈ G) :
    volume {t : ℝ | (l, t) ∈ E} ≤
      ENNReal.ofReal (((labeledTimeMarks D a G E p (coefficientCode p (a l))).card : ℝ) /
        (D : ℝ)) := by
  classical
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  let J := labeledTimeMarks D a G E p (coefficientCode p (a l))
  have hsub : {t : ℝ | (l, t) ∈ E} ⊆ ⋃ j ∈ J, timeCell D j := by
    intro t ht
    rcases exists_timeCell hD (hunit ht).2 with ⟨j, hj⟩
    have hjJ : j ∈ J := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, l, hl, rfl, t, ht, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, hj⟩⟩
  calc
    volume {t : ℝ | (l, t) ∈ E} ≤ volume (⋃ j ∈ J, timeCell D j) := measure_mono hsub
    _ ≤ ∑ j ∈ J, volume (timeCell D j) := measure_biUnion_finset_le _ _
    _ = ∑ _j ∈ J, ENNReal.ofReal (1 / (D : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [timeCell, Real.volume_Icc]
      congr 1
      ring
    _ = ENNReal.ofReal ((J.card : ℝ) / (D : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

end
end Submission.Obl.k4_scalar_coefficient_clustering
