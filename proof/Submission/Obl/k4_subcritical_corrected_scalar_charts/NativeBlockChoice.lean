/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeBlockChoice.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.BlockSelection
import Submission.Obl.k4_subcritical_corrected_scalar_charts.WitnessInheritance

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- Freeze one actual native entry for each endpoint chart and original time
block. The current law loses only the list factor; all closed-block overlaps
are handled by original product domination. -/
theorem exists_native_block_choice {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (σ : Measure (α × ℝ)) (C : ENNReal)
    (hdom : σ ≤ C • (ν.prod volume)) (T nH n : ℕ)
    (AH : Fin nH → Set α) (hAH : ∀ h, MeasurableSet (AH h))
    (hdisj : Pairwise (fun h h' => Disjoint (AH h) (AH h')))
    (B : Fin n → Set α) (hB : ∀ i, MeasurableSet (B i))
    (j : Fin n → Fin (2 ^ T)) (paired : Fin nH → Fin n → Prop)
    {K : ℝ} (hK : 0 ≤ K)
    (hcard : ∀ h block,
      ({i : Fin n | paired h i ∧ j i = block}.ncard : ℝ) ≤ K)
    (hcover : ∀ᵐ p ∂σ, ∃ h i, p.1 ∈ AH h ∧ p.1 ∈ B i ∧ p.2 ∈ I T (j i) ∧ paired h i) :
    ∃ choice : Fin nH → Fin (2 ^ T) → Option (Fin n),
      (∀ h block i, choice h block = some i → paired h i ∧ j i = block) ∧
      ∃ σ' : Measure (α × ℝ), σ' ≤ σ ∧
        σ univ ≤ ENNReal.ofReal K * σ' univ ∧
        ∀ᵐ p ∂σ', ∃ h i, p.1 ∈ AH h ∧ p.1 ∈ B i ∧ p.2 ∈ I T (j i) ∧
          choice h (j i) = some i := by
  classical
  let G := Fin nH × Fin (2 ^ T)
  let S := fun g : G => AH g.1 ×ˢ I T g.2
  let E := fun (_g : G) (i : Fin n) => B i ×ˢ I T (j i)
  let F := fun g : G => Finset.univ.filter fun i => paired g.1 i ∧ j i = g.2
  have hunique : ∀ᵐ p ∂σ, ∀ g g' : G, p ∈ S g → p ∈ S g' → g = g' := by
    have hd : ∀ g g' : G, g ≠ g' → g.2 = g'.2 → Disjoint (AH g.1) (AH g'.1) := by
      intro g g' hne hj
      apply hdisj
      intro hh
      exact hne (Prod.ext hh hj)
    filter_upwards [true_assignments_ae_unique ν σ C hdom T Prod.snd (fun g : G => AH g.1) hd]
      with p hp
    intro g g' hg hg'
    exact hp g g' hg.1 hg.2 hg'.1 hg'.2
  have hSd : Pairwise (fun g g' : G => AEDisjoint σ (S g) (S g')) := by
    intro g g' hne
    have hh : ∀ᵐ p ∂σ, p ∉ S g ∩ S g' := by
      filter_upwards [hunique] with p hp
      exact fun hmem => hne (hp g g' hmem.1 hmem.2)
    simpa only [AEDisjoint, ae_iff, not_not, Set.ofPred_mem_eq] using hh
  have htotal : ∀ᵐ p ∂σ, ∃ g : G, p ∈ S g := by
    filter_upwards [hcover] with p hp
    obtain ⟨h, i, hh, _, hi, _⟩ := hp
    exact ⟨(h, j i), hh, hi⟩
  have hlocal (g : G) : ∀ᵐ p ∂σ, p ∈ S g → ∃ i ∈ F g, p ∈ E g i := by
    filter_upwards [hcover, hunique] with p hp hu
    intro hpg
    obtain ⟨h, i, hh, hBi, hti, hpair⟩ := hp
    have hg : g = (h, j i) := hu g (h, j i) hpg ⟨hh, hti⟩
    refine ⟨i, ?_, hBi, hti⟩
    rw [hg]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair, rfl⟩
  obtain ⟨choice, hchoice, hm, hmass⟩ := exists_block_list_selection σ S E F hK
    (fun g => (hAH g.1).prod measurableSet_Icc)
    (fun _ i => (hB i).prod measurableSet_Icc) hSd htotal hlocal
    (fun g => by
      have heq : {i : Fin n | paired g.1 i ∧ j i = g.2} = (F g : Set (Fin n)) := by
        ext i
        simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, mem_setOf_eq]
      simpa only [heq, Set.ncard_coe_finset] using hcard g.1 g.2)
  let U := ⋃ g : G, S g ∩ optionalEvent (E g) (choice g)
  refine ⟨fun h block => choice (h, block), ?_, σ.restrict U, Measure.restrict_le_self, ?_, ?_⟩
  · intro h block i hi
    exact (Finset.mem_filter.mp (hchoice (h, block) i hi)).2
  · simpa only [Measure.restrict_apply_univ] using hmass
  · filter_upwards [ae_restrict_mem hm] with p hp
    obtain ⟨g, hpg, hpe⟩ := mem_iUnion.mp hp
    cases hi : choice g with
    | none => simp only [hi, optionalEvent, Set.mem_empty_iff_false] at hpe
    | some i =>
      have hFi := (Finset.mem_filter.mp (hchoice g i hi)).2
      have hpi : p ∈ E g i := by simpa only [hi, optionalEvent] using hpe
      refine ⟨g.1, i, hpg.1, hpi.1, hpi.2, ?_⟩
      rw [hFi.2]
      exact hi

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
