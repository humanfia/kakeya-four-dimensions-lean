-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.DenseCellRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BroadPieceCount

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set
open scoped Classical

/-- Remove only whole row-cell pieces whose measure is below a threshold.
The total cost is the threshold times the tube-cell crossing count. -/
theorem dense_cell_row_refinement {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n N : ℕ} (Y : Fin N → Fin n → Set X)
    (hY : ∀ j i, MeasurableSet (Y j i)) (hfin : ∀ j i, μ (Y j i) ≠ ⊤)
    {τ L : ℝ} (hτ : 0 ≤ τ)
    (hcross : ∀ i, ({j | (Y j i).Nonempty}.ncard : ℝ) ≤ L)
    (hbudget : τ * n * L ≤ (1 / 2 : ℝ) * ∑ j, ∑ i, (μ (Y j i)).toReal) :
    ∃ U : Fin N → Fin n → Set X,
      (∀ j i, MeasurableSet (U j i) ∧ U j i ⊆ Y j i ∧ (U j i = Y j i ∨ U j i = ∅)) ∧
      (1 / 2 : ℝ) * (∑ j, ∑ i, (μ (Y j i)).toReal) ≤ ∑ j, ∑ i, (μ (U j i)).toReal ∧
      (∀ j i, (U j i).Nonempty → ENNReal.ofReal τ ≤ μ (U j i)) := by
  let U : Fin N → Fin n → Set X := fun j i =>
    if τ ≤ (μ (Y j i)).toReal then Y j i else ∅
  have hU (j : Fin N) (i : Fin n) :
      MeasurableSet (U j i) ∧ U j i ⊆ Y j i ∧ (U j i = Y j i ∨ U j i = ∅) := by
    by_cases hh : τ ≤ (μ (Y j i)).toReal
    · simpa [U, hh] using hY j i
    · simp [U, hh]
  have hpoint (j : Fin N) (i : Fin n) : (μ (Y j i)).toReal ≤
      (μ (U j i)).toReal + τ * (if (Y j i).Nonempty then 1 else 0) := by
    by_cases hh : τ ≤ (μ (Y j i)).toReal
    · rw [show U j i = Y j i by simp only [U, if_pos hh]]
      apply le_add_of_nonneg_right
      exact mul_nonneg hτ (by split_ifs <;> norm_num)
    · rw [show U j i = ∅ by simp only [U, if_neg hh], measure_empty, ENNReal.toReal_zero, zero_add]
      by_cases hne : (Y j i).Nonempty
      · rw [if_pos hne, mul_one]
        exact le_of_not_ge hh
      · rw [if_neg hne, mul_zero, not_nonempty_iff_eq_empty.mp hne, measure_empty, ENNReal.toReal_zero]
  have hcard (j : Fin N) :
      (∑ i : Fin n, if (Y j i).Nonempty then (1 : ℝ) else 0) =
        ({i | (Y j i).Nonempty}.ncard : ℝ) := by
    have he : {i | (Y j i).Nonempty} = (Finset.univ.filter fun i => (Y j i).Nonempty : Set (Fin n)) := by
      ext i
      simp
    rw [he, ncard_coe_finset, ← Finset.sum_filter]
    simp
  have hcost : (∑ j, ∑ i : Fin n, τ * (if (Y j i).Nonempty then (1 : ℝ) else 0)) ≤ τ * n * L := by
    simp_rw [← Finset.mul_sum, hcard]
    rw [BrushPlanarity.piece_incidence_sum (fun j i => (Y j i).Nonempty)]
    calc
      _ ≤ τ * ∑ _i : Fin n, L := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hcross i)) hτ
      _ = _ := by simp; ring
  have htotal : (∑ j, ∑ i, (μ (Y j i)).toReal) ≤
      (∑ j, ∑ i, (μ (U j i)).toReal) + τ * n * L := by
    calc
      _ ≤ ∑ j, ∑ i, ((μ (U j i)).toReal + τ * (if (Y j i).Nonempty then 1 else 0)) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hpoint j i))
      _ = (∑ j, ∑ i, (μ (U j i)).toReal) +
          ∑ j, ∑ i : Fin n, τ * (if (Y j i).Nonempty then 1 else 0) := by simp only [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hcost
  refine ⟨U, hU, by linarith, ?_⟩
  intro j i hi
  by_cases hh : τ ≤ (μ (Y j i)).toReal
  · rw [show U j i = Y j i by simp only [U, if_pos hh]]
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin j i)).mpr hh
  · exfalso
    apply Set.not_nonempty_empty
    simpa only [U, if_neg hh] using hi

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
