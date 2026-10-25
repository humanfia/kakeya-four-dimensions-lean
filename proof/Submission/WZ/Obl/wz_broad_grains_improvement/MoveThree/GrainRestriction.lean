-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainRestriction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainRestriction.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Mono
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber fiberBodyCount measurable_assignedFiber assignedFiber_mono
   assignedFiber_restrict grain_refinement_transfer)

noncomputable section

/-- Cutting every fine shading by a common set in its assigned fibre preserves
pointwise broadness, with exactly the same error. -/
theorem broad_restrict_fibres {ω ζ δ h ρ : ℝ} {n N : ℕ}
    {v : Fin n → V} {S : Finset (Fin n)} {Z : Fin n → Set V}
    {f : Fin n → Fin N} (C : Fin N → Set V)
    (hB : Broad ω ζ δ h ρ n N v S Z f) :
    Broad ω ζ δ h ρ n N v S (fun i => Z i ∩ C (f i)) f := by
  classical
  intro k p u r hu hdr hrρ
  by_cases hp : p ∈ C k
  · have hnum : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ C (f i) ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} := by
      ext i
      simp only [mem_ofPred_eq, mem_inter_iff]
      aesop
    have hden : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ C (f i)} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i} := by
      ext i
      simp only [mem_ofPred_eq, mem_inter_iff]
      aesop
    simpa only [hnum, hden] using hB k p u r hu hdr hrρ
  · have hnum : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ C (f i) ∧
        min ‖v i - u‖ ‖v i + u‖ ≤ r} = (∅ : Set (Fin n)) := by
      ext i
      simp only [mem_ofPred_eq, mem_inter_iff, mem_empty_iff_false, iff_false]
      aesop
    have hden : {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∩ C (f i)} = (∅ : Set (Fin n)) := by
      ext i
      simp only [mem_ofPred_eq, mem_inter_iff, mem_empty_iff_false, iff_false]
      aesop
    simp only [hnum, hden, q, Set.ncard_empty, Nat.cast_zero, mul_zero, le_refl]

/-- The mass transfer lemma can be strengthened to the explicit full-fibre
restriction. This form also preserves all pointwise fibre counts and broadness. -/
theorem grain_refinement_transfer_full {n N L : ℕ}
    (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Z : Fin n → Set V) (H H' : Fin L → Set V) {m t : ℝ}
    (hm : 0 ≤ m) (ht : 0 ≤ t)
    (hZm : ∀ i, MeasurableSet (Z i)) (hHm : ∀ j, MeasurableSet (H j))
    (hH'm : ∀ j, MeasurableSet (H' j)) (hH'H : ∀ j, H' j ⊆ H j)
    (hdisj : ∀ i j, i ≠ j → γ i = γ j → Disjoint (H i) (H j))
    (heq : ∀ k, assignedFiber γ H k = assignedFiber f Z k)
    (hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m)
    (hretain : O t * ∑ j, μ (H j) ≤ ∑ j, μ (H' j)) :
    let W := fun i => Z i ∩ assignedFiber γ H' (f i)
    (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
      O (t / 2) * ∑ i, μ (Z i) ≤ ∑ i, μ (W i) ∧
      ∀ k, assignedFiber f W k = assignedFiber γ H' k := by
  dsimp only
  obtain ⟨W, hW, hWmass, hWfib⟩ := grain_refinement_transfer f γ Z H H' hm ht
    hZm hHm hH'm hH'H hdisj heq hlevel hretain
  refine ⟨fun i => ⟨(hZm i).inter (measurable_assignedFiber γ hH'm (f i)),
    inter_subset_left⟩, hWmass.trans ?_, ?_⟩
  · apply Finset.sum_le_sum
    intro i _
    apply measure_mono
    intro p hp
    refine ⟨(hW i).2 hp, ?_⟩
    rw [← hWfib (f i)]
    exact ⟨i, rfl, hp⟩
  · apply assignedFiber_restrict
    intro k
    exact (assignedFiber_mono γ hH'H k).trans (heq k).subset

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
