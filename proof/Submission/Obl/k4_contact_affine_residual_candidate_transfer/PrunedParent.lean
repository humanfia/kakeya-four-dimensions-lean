/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/PrunedParent.lean. Original attribution comments are retained below. -/
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ParentCore
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StablePruning

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Simultaneous original-reference pruning followed by selection of one
successful parent. Every descendant floor is measured by the same original
law, after the final parent has been chosen. -/
theorem exists_pruned_parent_history_core
    {Ω R I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (G : Set Ω) (hG : MeasurableSet G)
    (event : I → Set Ω) (hevent : ∀ i, MeasurableSet (event i))
    (root : R → Set Ω) (rootIndex : R → I) (hroot : ∀ r, event (rootIndex r) = root r)
    (ancestor : I → R) (hsub : ∀ i, event i ⊆ root (ancestor i))
    (hunique : ∀ p ∈ G, ∀ r r', p ∈ root r → p ∈ root r' → r = r')
    (hcover : ∀ p ∈ G, ∃ r, p ∈ root r)
    (w : I → ℝ≥0∞) (hcost : ∑ i, w i < μ G) :
    ∃ (r : R) (C : Set Ω), MeasurableSet C ∧ C.Nonempty ∧ C ⊆ G ∧ C ⊆ root r ∧
      w (rootIndex r) ≤ μ C ∧
      ∀ i, (event i ∩ C).Nonempty → event i ⊆ root r ∧ w i ≤ μ (event i ∩ C) := by
  classical
  obtain ⟨G', hG', hGsub, hmass, hfloor⟩ :=
    Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning.simultaneous_cell_pruning
      μ event w Finset.univ (fun i _ => hevent i) G hG
  have hpos : μ G' ≠ 0 := by
    intro hz
    rw [hz, zero_add] at hmass
    exact (not_le_of_gt hcost) hmass
  have hnonempty : G'.Nonempty := nonempty_of_measure_ne_zero hpos
  have hfloor' : ∀ i, (event i ∩ G').Nonempty → w i ≤ μ (event i ∩ G') := by
    intro i hi
    rcases hfloor i (Finset.mem_univ i) with hempty | hf
    · exfalso
      obtain ⟨p, hp, hp'⟩ := hi
      have : p ∈ G' ∩ event i := ⟨hp', hp⟩
      simp only [hempty, mem_empty_iff_false] at this
    · simpa only [inter_comm] using hf
  have hrFloor : ∀ r, (G' ∩ root r).Nonempty → w (rootIndex r) ≤ μ (G' ∩ root r) := by
    intro r hr
    have heq : G' ∩ root r = event (rootIndex r) ∩ G' := by rw [hroot r, inter_comm]
    rw [heq]
    exact hfloor' (rootIndex r) (by rwa [heq] at hr)
  obtain ⟨r, C, hCm, hCne, hCG', hCr, hmassC, hdesc⟩ :=
    exists_parent_core μ G' hG' hnonempty root
      (fun r => hroot r ▸ hevent (rootIndex r))
      (fun p hp => hcover p (hGsub hp)) event ancestor hsub
      (fun p hp => hunique p (hGsub hp)) w hfloor'
      (fun r => w (rootIndex r)) hrFloor
  exact ⟨r, C, hCm, hCne, hCG'.trans hGsub, hCr, hmassC, hdesc⟩

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
