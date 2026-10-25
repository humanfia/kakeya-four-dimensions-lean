-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedCells.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedCells.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedCells.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripFarOverlaps

/-! Merge the velocity-only priority pieces sharing one coarse parameter bin.
The resulting cells form a disjoint whole-trajectory partition, even when the
fine heavy net itself has a fixed-power number of members. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open Submission.Lib.K4FinitePlankAtlases
open scoped RealInnerProductSpace BigOperators

def stripParameterCodes {m : ℕ} (r : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ) :
    Finset StripParameterCode := by
  classical
  exact Finset.univ.image (fun i => stripParameterCode r (n i) (β i))

abbrev StripCodeLabel {m : ℕ} (r : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ) :=
  {q : StripParameterCode // q ∈ stripParameterCodes r n β}

def canonicalStripIndex {m : ℕ} (r : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ)
    (q : StripCodeLabel r n β) : Fin m :=
  (Finset.mem_image.mp q.property).choose

theorem canonicalStripIndex_code {m : ℕ} (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (q : StripCodeLabel r n β) :
    stripParameterCode r (n (canonicalStripIndex r n β q))
      (β (canonicalStripIndex r n β q)) = q.val :=
  (Finset.mem_image.mp q.property).choose_spec.2

theorem stripCodeLabel_card_le {m : ℕ} (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) :
    Fintype.card (StripCodeLabel r n β) ≤ m := by
  classical
  simpa only [StripCodeLabel, Fintype.card_coe] using
    (show (stripParameterCodes r n β).card ≤ m from
      (Finset.card_image_le).trans (by simp))

def mergedStripCell {m : ℕ} (r : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ)
    (w : ℝ) (q : StripCodeLabel r n β) : Set StripSpace :=
  ⋃ i : {i : Fin m // stripParameterCode r (n i) (β i) = q.val},
    firstAssignment (fun j => affineStrip (n j) (β j) w) i.val

theorem mem_mergedStripCell {m : ℕ} {r : ℝ}
    {n : Fin m → StripSpace} {β : Fin m → ℝ} {w : ℝ}
    {q : StripCodeLabel r n β} {x : StripSpace} :
    x ∈ mergedStripCell r n β w q ↔
      ∃ i : Fin m, stripParameterCode r (n i) (β i) = q.val ∧
        x ∈ firstAssignment (fun j => affineStrip (n j) (β j) w) i := by
  simp only [mergedStripCell, Set.mem_iUnion, Subtype.exists, exists_prop]

theorem measurableSet_mergedStripCell {m : ℕ} (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ)
    (q : StripCodeLabel r n β) : MeasurableSet (mergedStripCell r n β w q) := by
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_firstAssignment _ (fun j => measurableSet_affineStrip _ _ _) _

theorem mergedStripCell_disjoint {m : ℕ} (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ) :
    Pairwise (fun q q' : StripCodeLabel r n β =>
      Disjoint (mergedStripCell r n β w q) (mergedStripCell r n β w q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨i, hi, hxi⟩ := mem_mergedStripCell.mp hx
  obtain ⟨j, hj, hxj⟩ := mem_mergedStripCell.mp hx'
  by_cases hij : i = j
  · subst j
    exact hne (Subtype.ext (hi.symm.trans hj))
  · exact Set.disjoint_left.mp (firstAssignment_disjoint _ hij) hxi hxj

theorem iUnion_mergedStripCell {m : ℕ} (r : ℝ)
    (n : Fin m → StripSpace) (β : Fin m → ℝ) (w : ℝ) :
    (⋃ q : StripCodeLabel r n β, mergedStripCell r n β w q) =
      ⋃ i, affineStrip (n i) (β i) w := by
  classical
  rw [← iUnion_firstAssignment]
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, hi, hxi⟩ := mem_mergedStripCell.mp hq
    exact Set.mem_iUnion.mpr ⟨i, hxi⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hcode : stripParameterCode r (n i) (β i) ∈ stripParameterCodes r n β :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨_, hcode⟩, mem_mergedStripCell.mpr ⟨i, rfl, hi⟩⟩

theorem mergedStripCell_velocity_bound {m : ℕ} {r : ℝ}
    {n : Fin m → StripSpace} {β : Fin m → ℝ} {w T : ℝ}
    {q : StripCodeLabel r n β} {x : StripSpace}
    (hr : 0 < r) (hT : 0 ≤ T) (hx : ‖x‖ ≤ T)
    (hmem : x ∈ mergedStripCell r n β w q) :
    x ∈ affineStrip (n (canonicalStripIndex r n β q))
      (β (canonicalStripIndex r n β q)) (w + 3 * (1 + T) * r) := by
  obtain ⟨i, hi, hxi⟩ := mem_mergedStripCell.mp hmem
  have hclose := stripParametersClose_of_code_eq hr
    (hi.trans (canonicalStripIndex_code r n β q).symm)
  have h := affineStrip_mem_of_close_parameters hT hx hclose hxi.1
  convert h using 1 <;> ring

/-- The bin selected by any velocity-priority piece is in a constant list
computed from the fine-state prediction, outside the fixed overlap event. -/
theorem mergedStripCell_code_predicted {m : ℕ}
    {n : Fin m → StripSpace} {β : Fin m → ℝ} {w r r₀ r₁ T : ℝ}
    {a : StripSpace} {b : ℝ} {x : StripSpace} {q : StripCodeLabel r n β}
    (hr : 0 < r) (hr₁ : r₁ ≤ r) (hT : 0 ≤ T) (hx : ‖x‖ ≤ T)
    (hraw : x ∈ affineStrip a b r₀)
    (hnet : ∃ j, stripParametersClose a b (n j) (β j) r₁)
    (hwidth : r₀ + (1 + T) * r₁ ≤ w)
    (hmem : x ∈ mergedStripCell r n β w q)
    (hgood : x ∉ stripFarOverlap n β w r T) :
    q.val ∈ stripParameterList r a b 2 := by
  obtain ⟨i, hi, hxi⟩ := mem_mergedStripCell.mp hmem
  obtain ⟨j, hj⟩ := hnet
  have hclose := raw_strip_prediction_close hT hx hraw hj hwidth hxi.1 hgood
  have hclose' : stripParametersClose a b (n i) (β i) ((2 : ℕ) * r) := by
    norm_num only [Nat.cast_ofNat]
    rcases hclose with h | h
    · exact Or.inl (h.trans (by linarith))
    · exact Or.inr (h.trans (by linarith))
  rw [← hi]
  exact stripParameterCode_mem_list hr hclose'

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
