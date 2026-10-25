-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/FiniteOriginalAssignments.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/FiniteOriginalAssignments.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Lib.K4FinitePlankAtlases.Assignments
import Submission.Lib.K4ScalarCoreAssembly.MeasurableMenuChoice
import Submission.Lib.K4MeshJitter.Pairs
import Submission.Obl.k4_general_parent_projected_layers.Model

/-! Actual measurable assignments into disjoint original finite witness families. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open Submission.Lib.K4FinitePlankAtlases
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- Finite measurable coverage supplies a measurable original assignment into
the accepted priority-disjoint witnesses. The entire original law is partitioned. -/
theorem exists_original_first_assignment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hμ : μ univ ≠ 0) {n : ℕ}
    (W : Fin n → Set Ω) (hW : ∀ i, MeasurableSet (W i))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ W i) :
    ∃ index : Ω → Fin n, Measurable index ∧
      (∀ᵐ p ∂μ, p ∈ firstAssignment W (index p)) ∧
      (∑ i, μ.restrict (firstAssignment W i)) = μ := by
  classical
  obtain ⟨p₀, -, i₀, -⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hμ
    (by simpa using hcover : ∀ᵐ p ∂μ.restrict univ, ∃ i, p ∈ W i)
  letI : Nonempty (Fin n) := ⟨i₀⟩
  let A : Set Ω := ⋃ i, W i
  have hvalid (p : Ω) (hp : p ∈ A) : ∃ i ∈ (Finset.univ : Finset (Fin n)), p ∈ firstAssignment W i := by
    change p ∈ ⋃ i, W i at hp
    rw [← iUnion_firstAssignment W] at hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨i, Finset.mem_univ _, hi⟩
  obtain ⟨index, hindex, hchosen⟩ := Submission.Lib.K4ScalarCoreAssembly.exists_measurable_finite_menu_choice
    Finset.univ (fun i p => p ∈ firstAssignment W i)
    (measurableSet_firstAssignment W hW) A hvalid
  have hi : Measurable index := fun E _ => hindex (fun i => i ∈ E)
  have hmem : ∀ᵐ p ∂μ, p ∈ firstAssignment W (index p) := by
    filter_upwards [hcover] with p hp
    exact (hchosen p (mem_iUnion.mpr hp)).2
  refine ⟨index, hi, hmem, ?_⟩
  exact Submission.Lib.K4MeshJitter.partition_restrict_sum μ (firstAssignment W)
    (measurableSet_firstAssignment W hW) (firstAssignment_disjoint W)
    (hmem.mono fun p hp => ⟨index p, hp⟩)

def trueWitness {α : Type} [MeasurableSpace α] (a : PreparedModel α)
    (k : ℕ) (s : ℝ) (i : Fin (a.n k s)) : Set (α × ℝ) := a.B k s i ×ˢ a.block k s i

/-- The actual closed true-label blocks have disjoint measurable incidence
assignments, including when their endpoints overlap. No individual current
assignment floor is asserted before the original reference pruning step. -/
theorem prepared_true_first_assignment {α : Type} [MeasurableSpace α]
    (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (hcommon : a.Common p)
    {R : ℝ} {k : ℕ} {s : ℝ} (hatlas : a.AtlasAt p R k s) :
    ∃ index : α × ℝ → Fin (a.n k s), Measurable index ∧
      (∀ᵐ z ∂a.mu k, z ∈ firstAssignment (trueWitness a k s) (index z)) ∧
      (∑ i, (a.mu k).restrict (firstAssignment (trueWitness a k s) i)) = a.mu k := by
  have hK : 0 < p.K k := zero_lt_one.trans_le (hp.2.2.1.1 k)
  rcases hcommon k with ⟨_, _, _, _, hρ, _, hmass, _⟩
  have hμ : a.mu k univ ≠ 0 := ne_of_gt
    ((ENNReal.ofReal_pos.mpr (inv_pos.mpr hK)).trans_le (hmass.trans (hρ univ)))
  rcases hatlas with ⟨_, _, hsets, _, _, hcover, _⟩
  apply exists_original_first_assignment (a.mu k) hμ (trueWitness a k s)
  · intro i
    exact (hsets i).2.1.prod measurableSet_Icc
  · exact hcover

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
