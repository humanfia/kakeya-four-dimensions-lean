-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PieceRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoreLevel

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

open MeasureTheory Set

/-- A subshading can be transferred to finite geometric pieces by intersecting
with its union. Incidence implications, including full-carrier crossings, survive. -/
theorem finite_piece_subshading {n : ℕ} {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (U H : ι → Set V) (Z W : Fin n → Set V) (C : Fin n → ι → Prop)
    (hW : ∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i)
    (hH : ∀ j ∈ F, MeasurableSet (H j))
    (hunion : (⋃ j ∈ F, H j) = ⋃ i, Z i)
    (hcross : ∀ i j, j ∈ F → (Z i ∩ H j).Nonempty →
      Z i ∩ U j ⊆ H j ∧ C i j) :
    ∃ (F' : Finset ι) (H' : ι → Set V),
      F' ⊆ F ∧ (∀ j, H' j ⊆ H j) ∧
      (∀ j ∈ F', MeasurableSet (H' j) ∧ (H' j).Nonempty) ∧
      (⋃ j ∈ F', H' j) = ⋃ i, W i ∧
      (∀ i j, j ∈ F' → (W i ∩ H' j).Nonempty →
        W i ∩ U j ⊆ H' j ∧ C i j) := by
  classical
  let H' : ι → Set V := fun j => H j ∩ ⋃ i, W i
  let F' := F.filter (fun j => (H' j).Nonempty)
  have hFF : F' ⊆ F := Finset.filter_subset _ _
  refine ⟨F', H', hFF, (fun _ => inter_subset_left), ?_, ?_, ?_⟩
  · intro j hj
    exact ⟨(hH j (hFF hj)).inter (MeasurableSet.iUnion fun i => (hW i).1),
      (Finset.mem_filter.mp hj).2⟩
  · ext p
    constructor
    · intro hp
      obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp hp
      exact hpj.2
    · intro hp
      obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
      have hpZ : p ∈ ⋃ i, Z i := mem_iUnion.mpr ⟨i, (hW i).2 hpi⟩
      obtain ⟨j, hj, hpj⟩ := mem_iUnion₂.mp (hunion ▸ hpZ)
      have hpH : p ∈ H' j := ⟨hpj, hp⟩
      exact mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, ⟨p, hpH⟩⟩, hpH⟩
  · intro i j hj hmeet
    obtain ⟨p, hpi, hpj⟩ := hmeet
    have hc := hcross i j (hFF hj) ⟨p, (hW i).2 hpi, hpj.1⟩
    refine ⟨?_, hc.2⟩
    intro q hq
    exact ⟨hc.1 ⟨(hW i).2 hq.1, hq.2⟩, mem_iUnion.mpr ⟨i, hq.1⟩⟩

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
