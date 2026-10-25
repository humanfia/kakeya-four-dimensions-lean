-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BadIncidences.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory
open scoped ENNReal

/-- Either one object has a substantial set of forbidden incidences, or
removing all forbidden incidences retains half of every object's mass. -/
theorem remove_bad_incidences {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {n : ℕ}
    (H : Fin n → Set Ω) (R : Fin n → Fin n → Prop) (t : Fin n → ℝ≥0∞)
    (hHm : ∀ i, MeasurableSet (H i)) (hfin : ∀ i, ν (H i) ≠ ⊤)
    (ht : ∀ i, t i ≤ (1 / 2 : ℝ≥0∞) * ν (H i)) :
    (∃ (i : Fin n) (A : Set Ω), MeasurableSet A ∧ A ⊆ H i ∧ t i ≤ ν A ∧
      ∀ p ∈ A, ∃ j, R i j ∧ p ∈ H j) ∨
    (∃ G : Fin n → Set Ω,
      (∀ i, MeasurableSet (G i) ∧ G i ⊆ H i ∧ (1 / 2 : ℝ≥0∞) * ν (H i) ≤ ν (G i)) ∧
      ∀ i j p, p ∈ G i → p ∈ G j → ¬ R i j) := by
  classical
  let B := fun i => ⋃ j, if R i j then H j else ∅
  have hBm (i : Fin n) : MeasurableSet (B i) := by
    apply MeasurableSet.iUnion
    intro j
    by_cases h : R i j
    · simpa only [if_pos h] using hHm j
    · simp only [if_neg h]
      exact MeasurableSet.empty
  by_cases hbad : ∃ i, t i ≤ ν (H i ∩ B i)
  · obtain ⟨i, hi⟩ := hbad
    left
    refine ⟨i, H i ∩ B i, (hHm i).inter (hBm i), inter_subset_left, hi, ?_⟩
    intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp.2
    by_cases h : R i j
    · exact ⟨j, h, by simpa only [if_pos h] using hj⟩
    · simp only [if_neg h, mem_empty_iff_false] at hj
  · right
    let G := fun i => H i \ B i
    refine ⟨G, ?_, ?_⟩
    · intro i
      refine ⟨(hHm i).diff (hBm i), sdiff_subset, ?_⟩
      have hsmall : ν (H i ∩ B i) ≤ (1 / 2 : ℝ≥0∞) * ν (H i) :=
        (le_of_lt (lt_of_not_ge (fun h => hbad ⟨i, h⟩))).trans (ht i)
      exact half_mass_after_loss (hfin i) (measure_sdiff_add_inter (H i) (hBm i)).ge hsmall
    · intro i j p hi hj hij
      apply hi.2
      exact mem_iUnion.mpr ⟨j, by simpa only [if_pos hij] using hj.1⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
