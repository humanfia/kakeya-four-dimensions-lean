/- Adapted from this LOT tree, obligation o260, session x0919, commit 57638ddd7c07709143f61bbedd02efd72974929b,
   Submission/Obl/k4_contact_shifted_quadratic_candidates/ParentCore.lean. Original attribution comments are retained below. -/
import Mathlib

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- One observed intersection identifies the ancestor of a whole history.
Uniqueness is needed only at points of the retained source. -/
theorem history_subset_selected_parent
    {Ω R I : Type*} (G : Set Ω) (root : R → Set Ω)
    (event : I → Set Ω) (ancestor : I → R)
    (hsub : ∀ i, event i ⊆ root (ancestor i))
    (hunique : ∀ p ∈ G, ∀ r r', p ∈ root r → p ∈ root r' → r = r')
    (r : R) (i : I) (hne : (event i ∩ (G ∩ root r)).Nonempty) :
    event i ⊆ root r := by
  obtain ⟨p, hpi, hpG, hpr⟩ := hne
  have heq : ancestor i = r := hunique p hpG _ _ (hsub i hpi) hpr
  simpa only [heq] using hsub i

/-- After choosing a parent, every surviving descendant keeps exactly its
preselection mass on the core. There is no additional averaging loss. -/
theorem history_mass_selected_parent
    {Ω R I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Set Ω) (root : R → Set Ω) (event : I → Set Ω) (ancestor : I → R)
    (hsub : ∀ i, event i ⊆ root (ancestor i))
    (hunique : ∀ p ∈ G, ∀ r r', p ∈ root r → p ∈ root r' → r = r')
    (r : R) (i : I) (hne : (event i ∩ (G ∩ root r)).Nonempty) :
    μ (event i ∩ (G ∩ root r)) = μ (event i ∩ G) := by
  congr 1
  have hi := history_subset_selected_parent G root event ancestor hsub hunique r i hne
  ext p
  exact ⟨fun hp => ⟨hp.1, hp.2.1⟩, fun hp => ⟨hp.1, hp.2, hi hp.1⟩⟩

/-- Original-reference floors survive restriction to a single successful
parent because each descendant is a whole subset of its prescribed ancestor. -/
theorem history_floor_selected_parent
    {Ω R I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Set Ω) (root : R → Set Ω) (event : I → Set Ω) (ancestor : I → R)
    (hsub : ∀ i, event i ⊆ root (ancestor i))
    (hunique : ∀ p ∈ G, ∀ r r', p ∈ root r → p ∈ root r' → r = r')
    (w : I → ℝ≥0∞) (hfloor : ∀ i, (event i ∩ G).Nonempty → w i ≤ μ (event i ∩ G))
    (r : R) :
    ∀ i, (event i ∩ (G ∩ root r)).Nonempty → w i ≤ μ (event i ∩ (G ∩ root r)) := by
  intro i hi
  rw [history_mass_selected_parent μ G root event ancestor hsub hunique r i hi]
  apply hfloor i
  exact hi.mono (fun p hp => ⟨hp.1, hp.2.1⟩)

/-- The parent may be any node met by the nonempty core. Its floor already
supplies the relative mass needed for subsequent normalization. -/
theorem exists_parent_core
    {Ω R I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (G : Set Ω) (hG : MeasurableSet G) (hGne : G.Nonempty)
    (root : R → Set Ω) (hroot : ∀ r, MeasurableSet (root r))
    (hcover : ∀ p ∈ G, ∃ r, p ∈ root r)
    (event : I → Set Ω) (ancestor : I → R)
    (hsub : ∀ i, event i ⊆ root (ancestor i))
    (hunique : ∀ p ∈ G, ∀ r r', p ∈ root r → p ∈ root r' → r = r')
    (w : I → ℝ≥0∞) (hfloor : ∀ i, (event i ∩ G).Nonempty → w i ≤ μ (event i ∩ G))
    (wr : R → ℝ≥0∞)
    (hrootfloor : ∀ r, (G ∩ root r).Nonempty → wr r ≤ μ (G ∩ root r)) :
    ∃ (r : R) (C : Set Ω), MeasurableSet C ∧ C.Nonempty ∧ C ⊆ G ∧ C ⊆ root r ∧
      wr r ≤ μ C ∧ ∀ i, (event i ∩ C).Nonempty →
        event i ⊆ root r ∧ w i ≤ μ (event i ∩ C) := by
  obtain ⟨p, hp⟩ := hGne
  obtain ⟨r, hpr⟩ := hcover p hp
  have hCne : (G ∩ root r).Nonempty := ⟨p, hp, hpr⟩
  refine ⟨r, G ∩ root r, hG.inter (hroot r), hCne,
    inter_subset_left, inter_subset_right, hrootfloor r hCne, ?_⟩
  intro i hi
  exact ⟨history_subset_selected_parent G root event ancestor hsub hunique r i hi,
    history_floor_selected_parent μ G root event ancestor hsub hunique w hfloor r i hi⟩

end

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
