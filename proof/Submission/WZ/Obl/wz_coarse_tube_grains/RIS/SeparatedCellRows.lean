-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SeparatedCellRows.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DenseCellRows
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.TubeCellSeparation

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set
open scoped Classical

/-- Remove sparse tube-cell rows, then select well-separated occupied cells
independently for each tube. The total mass cost is explicit. -/
theorem separated_dense_cell_refinement {δ r τ L : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r) (hτ : 0 < τ)
    {n N : ℕ} (x v : Fin n → Space) (Y : Fin N → Fin n → Set Space) (q : Fin N → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ j i, MeasurableSet (Y j i))
    (hfin : ∀ j i, volume (Y j i) ≠ ⊤)
    (hYT : ∀ j i, Y j i ⊆ Tube δ (x i) (v i) ∩ Metric.ball (q j) r)
    (hdisj : ∀ i, Pairwise fun j k => Disjoint (Y j i) (Y k i))
    (hcross : ∀ i, ({j | (Y j i).Nonempty}.ncard : ℝ) ≤ L)
    (hbudget : (τ * δ ^ 2 * r) * n * L ≤
      (1 / 2 : ℝ) * ∑ j, ∑ i, (volume (Y j i)).toReal) :
    ∃ Z : Fin N → Fin n → Set Space,
      (∀ j i, MeasurableSet (Z j i) ∧ Z j i ⊆ Y j i) ∧
      (∀ j i, (Z j i).Nonempty → ENNReal.ofReal (τ * δ ^ 2 * r) ≤ volume (Z j i)) ∧
      (∀ i j k, j ≠ k → (Z j i).Nonempty → (Z k i).Nonempty →
        10 * r < dist (q j) (q k)) ∧
      (∑ j, ∑ i, (volume (Y j i)).toReal) ≤
        (2 * (⌈422400 / τ⌉₊ : ℝ)) * (∑ j, ∑ i, (volume (Z j i)).toReal) := by
  obtain ⟨U, hU, hhalf, hdense⟩ := dense_cell_row_refinement volume Y hY hfin
    (by positivity : 0 ≤ τ * δ ^ 2 * r) hcross hbudget
  have hUfin (j : Fin N) (i : Fin n) : volume (U j i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin j i) (measure_mono (hU j i).2.1)
  have hex (i : Fin n) := tube_cell_separated_subfamily hδ hr hδr hτ
    (x i) (v i) (hv i) (fun j => U j i) q
    (fun j => (hU j i).1) (fun j => (hU j i).2.1.trans (hYT j i))
    (fun j k hjk => (hdisj i hjk).mono (hU j i).2.1 (hU k i).2.1)
    (fun j => hdense j i)
  choose S hS hsep hkeep using hex
  let Z : Fin N → Fin n → Set Space := fun j i => if j ∈ S i then U j i else ∅
  have hZ (j : Fin N) (i : Fin n) : MeasurableSet (Z j i) ∧ Z j i ⊆ U j i := by
    by_cases hj : j ∈ S i
    · simp only [Z, if_pos hj]
      exact ⟨(hU j i).1, subset_rfl⟩
    · simp only [Z, if_neg hj]
      exact ⟨MeasurableSet.empty, empty_subset _⟩
  have hmem (j : Fin N) (i : Fin n) (hj : (Z j i).Nonempty) : j ∈ S i := by
    by_contra hh
    apply Set.not_nonempty_empty
    simpa only [Z, if_neg hh] using hj
  have hZsum (i : Fin n) : (∑ j, (volume (Z j i)).toReal) =
      ∑ j ∈ S i, (volume (U j i)).toReal := by
    simp only [Z, apply_ite, measure_empty, ENNReal.toReal_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hkeepR (i : Fin n) : (∑ j, (volume (U j i)).toReal) ≤
      (⌈422400 / τ⌉₊ : ℝ) * ∑ j, (volume (Z j i)).toReal := by
    have hright : (⌈422400 / τ⌉₊ : ENNReal) * (∑ j ∈ S i, volume (U j i)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr (fun j _ => hUfin j i))
    have hh := ENNReal.toReal_mono hright (hkeep i)
    simpa only [ENNReal.toReal_sum (fun j _ => hUfin j i), ENNReal.toReal_mul,
      ENNReal.toReal_natCast, hZsum] using hh
  have htotal : (∑ j, ∑ i, (volume (U j i)).toReal) ≤
      (⌈422400 / τ⌉₊ : ℝ) * (∑ j, ∑ i, (volume (Z j i)).toReal) := by
    calc
      _ = ∑ i, ∑ j, (volume (U j i)).toReal := Finset.sum_comm
      _ ≤ ∑ i, (⌈422400 / τ⌉₊ : ℝ) * ∑ j, (volume (Z j i)).toReal :=
        Finset.sum_le_sum (fun i _ => hkeepR i)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  refine ⟨Z, fun j i => ⟨(hZ j i).1, (hZ j i).2.trans (hU j i).2.1⟩, ?_, ?_, ?_⟩
  · intro j i hj
    have hjS := hmem j i hj
    simpa only [Z, if_pos hjS] using hdense j i (hS i j hjS)
  · intro i j k hjk hj hk
    exact hsep i j (hmem j i hj) k (hmem k i hk) hjk
  · nlinarith [hhalf, htotal]

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
