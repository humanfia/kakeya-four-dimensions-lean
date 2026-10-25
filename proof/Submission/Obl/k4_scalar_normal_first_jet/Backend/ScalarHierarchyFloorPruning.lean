/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyFloorPruning.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyFloorPruning.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyFloorBudget
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarTimeGrid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.Pruning

/-! Simultaneous block floors, tested against one original hierarchy law. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

theorem original_scalar_hierarchy_floor_pruning {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Ico (0 : ℝ) 1) {n : ℕ}
    (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i) {K : ℝ} (hK : 0 < K) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      (ν.prod volume) (E \ R) ≤ ENNReal.ofReal ((n : ℝ) / K) ∧
      ∀ q ∈ R, ∀ i,
        ENNReal.ofReal ((1 / (J i : ℝ)) / K) ≤
          (ν.prod volume) (R ∩ (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2))) := by
  classical
  let C : (Σ i : Fin n, Fin (J i)) → Set (Λ × ℝ) :=
    fun ij => univ ×ˢ timeCell (J ij.1) ij.2
  let b : (Σ i : Fin n, Fin (J i)) → ENNReal :=
    fun ij => ENNReal.ofReal ((1 / (J ij.1 : ℝ)) / K)
  have hC ij : MeasurableSet (C ij) :=
    MeasurableSet.univ.prod (measurableSet_timeCell _ _)
  obtain ⟨R, hRm, hRE, hloss, hfloor⟩ :=
    exists_measurable_current_floor_pruning (ν.prod volume) C b hC hE
  refine ⟨R, hRm, hRE, ?_, ?_⟩
  · exact hloss.trans_eq (scalar_hierarchy_floor_budget J hJ hK)
  · intro q hq i
    let c := scalarTimeBlockCode (J i) (hJ i) q.2
    have hqc : q ∈ C ⟨i, c⟩ :=
      ⟨mem_univ _, (scalarTimeBlockCode_eq_iff (hJ i) c (hunit (hRE hq)).2).mp rfl⟩
    rcases hfloor ⟨i, c⟩ with he | hf
    · have hh : q ∈ (∅ : Set (Λ × ℝ)) := he ▸ ⟨hq, hqc⟩
      exact False.elim hh
    · exact hf.le

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
