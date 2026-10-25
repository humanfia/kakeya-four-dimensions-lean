import Submission.Obl.k4_raw_localized_native_systems.SourceForests
import Submission.Obl.k4_raw_critical_segment_forests.ParentAtlas
import Submission.Obl.k4_remainder_pure_profile_normalization.ObservationImages

/-
Adapted from this LOT tree, o197, session x0690, `SourceLists.lean` (commit
f7206748), renamed into this obligation's namespace.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Actual own-depth observable images supply a canonical measurable source
policy, independently of the original possibly nonmeasurable witness policy. -/
def sourceLists {p : Data} {k : ℕ}
    (a : k4_raw_critical_segment_forests.Forest p k) (r : ℕ → ℝ)
    (i : ℕ) (γ : Fin (p.W k)) (o : Observation) : Finset (Fin a.C) :=
  @Finset.filter (Fin a.C)
    (fun b => a.lev b = i ∧ a.γ b = γ ∧
      o ∈ obs (p.B k γ) (δ (p.N k) (r i)) '' a.F b)
    (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_sourceLists {p : Data} {k : ℕ}
    (a : k4_raw_critical_segment_forests.Forest p k) (r : ℕ → ℝ)
    (i : ℕ) (γ : Fin (p.W k)) (o : Observation) (b : Fin a.C) :
    b ∈ sourceLists a r i γ o ↔ a.lev b = i ∧ a.γ b = γ ∧
      o ∈ obs (p.B k γ) (δ (p.N k) (r i)) '' a.F b := by
  simp only [sourceLists, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The semialgebraic format of source events suffices for exact Borel lists. -/
theorem sourceLists_measurable {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    {a : k4_raw_critical_segment_forests.Forest p k}
    (ha : a.Core M D m r) (i : ℕ) (γ : Fin (p.W k)) (b : Fin a.C) :
    MeasurableSet {o | b ∈ sourceLists a r i γ o} := by
  classical
  by_cases hi : a.lev b = i
  · by_cases hγ : a.γ b = γ
    · have hfmt := (ha.2.2.2.2.2 b).2.2.1.2.2.2.2.2.2.2.2.1
      have himage : MeasurableSet (obs (p.B k γ) (δ (p.N k) (r i)) '' a.F b) :=
        k4_remainder_pure_profile_normalization.measurableSet_obs_image _ _
          (fun j => (hfmt j).2)
      simpa only [mem_sourceLists, hi, hγ, true_and, Set.setOf_mem_eq] using himage
    · have he : {o | b ∈ sourceLists a r i γ o} = ∅ := by
        ext o
        simp only [mem_sourceLists, hγ, false_and, and_false, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false]
      rw [he]
      exact MeasurableSet.empty
  · have he : {o | b ∈ sourceLists a r i γ o} = ∅ := by
      ext o
      simp only [mem_sourceLists, hi, false_and, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [he]
    exact MeasurableSet.empty

/-- Canonical actual-image lists are contained in any valid old policy at the
same depth and world, so they obey exactly its cardinal bound. -/
theorem sourceLists_subset {p : Data} {k : ℕ} {r : ℕ → ℝ}
    {a : k4_raw_critical_segment_forests.Forest p k}
    {lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)}
    (ha : a.Prepared r lst) (i : ℕ) (γ : Fin (p.W k)) (o : Observation) :
    sourceLists a r i γ o ⊆ lst i γ o := by
  intro b hb
  obtain ⟨hi, hγ, z, hz, hobs⟩ := (mem_sourceLists a r i γ o b).mp hb
  have hm := (ha.2 b).2 z hz
  rwa [hi, hγ, hobs] at hm

theorem sourceLists_prepared {p : Data} {k : ℕ} {r : ℕ → ℝ}
    {a : k4_raw_critical_segment_forests.Forest p k}
    {lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)}
    (ha : a.Prepared r lst) : a.Prepared r (sourceLists a r) := by
  constructor
  · intro i γ o
    exact (Nat.cast_le.mpr (Finset.card_le_card (sourceLists_subset ha i γ o))).trans
      (ha.1 i γ o)
  · intro b
    refine ⟨(ha.2 b).1, fun z hz => ?_⟩
    exact (mem_sourceLists a r _ _ _ b).mpr ⟨rfl, rfl, z, hz, rfl⟩

/-- A forest layer with the same original event and full assignment. -/
abbrev sourceLayer {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r) (i : ℕ) :
    Atlas p k := a.layerAtlas i (ha.j_lt · ·) (sourceLists a r)

/-- Terminal knowledge is obtained by the exact coarse-from-fine map; no event
or prior is changed when converting the own-depth policy. -/
theorem sourceLayer_known {p : Data} (hp : Valid p) {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r)
    {lst : ℕ → Fin (p.W k) → Observation → Finset (Fin a.C)}
    (hprep : a.Prepared r lst) {i : ℕ} (hi : i < m) (hr : r i ≤ p.L) :
    (k4_raw_critical_segment_forests.finerLists (sourceLayer a ha i) (r i)).KnownAt
      M D a.κ (r i) := by
  have hcanon := sourceLists_prepared hprep
  have hlayer := a.layer_prepared (sourceLists a r) hcanon i (ha.j_lt · ·)
  exact k4_raw_critical_segment_forests.knownAt_finer_of_trueDepth hp hr
    (a.layer_trueDepth ha hi (sourceLists a r)) hlayer.1 (fun b => (hlayer.2 b).2)

theorem sourceLayer_lists_measurable {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r)
    (i : ℕ) (γ : Fin (p.W k)) (b : Fin (sourceLayer a ha i).C) :
    MeasurableSet {o | b ∈ (sourceLayer a ha i).lst γ o} := by
  simpa only [sourceLayer, k4_raw_critical_segment_forests.Forest.layerAtlas,
    k4_raw_critical_segment_forests.Forest.layerLists, Finset.mem_filter,
    Finset.mem_univ, true_and] using
    sourceLists_measurable ha i γ (a.layerEmb i b)

theorem sourceLayer_terminal_lists_measurable {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r)
    (i : ℕ) (γ : Fin (p.W k))
    (b : Fin (k4_raw_critical_segment_forests.finerLists (sourceLayer a ha i) (r i)).C) :
    MeasurableSet {o | b ∈
      (k4_raw_critical_segment_forests.finerLists (sourceLayer a ha i) (r i)).lst γ o} := by
  exact (sourceLayer_lists_measurable a ha i γ b).preimage
    (Submission.Lib.K4Homogenization.measurable_coarsenObservation (p.N k) (r i) p.L)

end
end Submission.Obl.k4_raw_localized_native_systems
