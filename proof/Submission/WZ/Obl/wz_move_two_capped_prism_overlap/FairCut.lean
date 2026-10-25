-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.FairCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.MeasureCut
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.FiniteColors
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ShadingAtoms

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, FairCut.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V I)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

/-- An overlap bound on the labels permits disjoint cuts within each fibre.
Every one of a finite collection of test sets retains exactly the same
fraction of its volume. In particular, test sets may include both the
individual incidence pieces and the union shading of each prism. -/
theorem fair_fiber_cut {ι : Type*} [Fintype ι] {L N m : ℕ}
    (hm : 0 < m) (Y : ι → Set V) (hYm : ∀ i, MeasurableSet (Y i))
    (hYI : ∀ i, Y i ⊆ I) (f : ι → Fin L) (γ : Fin L → Fin N)
    (hcount : ∀ p k, ({j | γ j = k ∧ ∃ i, f i = j ∧ p ∈ Y i}.ncard) ≤ m) :
    ∃ C : Fin L → Set V, (∀ j, MeasurableSet (C j)) ∧
      (∀ j j', j ≠ j' → γ j = γ j' → Disjoint (C j) (C j')) ∧
      ∀ i, volume (Y i ∩ C (f i)) = (m : ENNReal)⁻¹ * volume (Y i) := by
  classical
  have hAI (A : Finset ι) : shadingAtom Y A ⊆ I :=
    inter_subset_left.trans (iUnion_subset hYI)
  choose D hD hDdisj using fun A : Finset ι =>
    exists_equal_volume_pieces m hm (shadingAtom_measurable hYm A) (hAI A)
  have hcolors (A : Finset ι) : ∃ color : Fin L → Fin m,
      (shadingAtom Y A).Nonempty → ∀ j ∈ A.image f, ∀ j' ∈ A.image f,
        γ j = γ j' → color j = color j' → j = j' := by
    by_cases hA : (shadingAtom Y A).Nonempty
    · obtain ⟨p, hp⟩ := hA
      have hcard (k : Fin N) : ((A.image f).filter fun j => γ j = k).card ≤ m := by
        have he : (↑((A.image f).filter fun j => γ j = k) : Set (Fin L)) =
            {j | γ j = k ∧ ∃ i, f i = j ∧ p ∈ Y i} := by
          ext j
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_image, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨⟨i, hi, hij⟩, hj⟩
            exact ⟨hj, i, hij, (hp.2 i).mpr hi⟩
          · rintro ⟨hj, i, hij, hi⟩
            exact ⟨⟨i, (hp.2 i).mp hi, hij⟩, hj⟩
        have hh := hcount p k
        rw [← he, Set.ncard_coe_finset] at hh
        exact hh
      obtain ⟨color, hcolor⟩ := finite_fiber_colors hm (A.image f) γ hcard
      exact ⟨color, fun _ => hcolor⟩
    · exact ⟨fun _ => ⟨0, hm⟩, fun h => (hA h).elim⟩
  choose color hcolor using hcolors
  let E : Finset ι → Fin L → Set V := fun A j =>
    if j ∈ A.image f then D A (color A j) else ∅
  have hEm (A : Finset ι) (j : Fin L) : MeasurableSet (E A j) := by
    dsimp [E]
    split_ifs
    · exact (hD A _).1
    · exact MeasurableSet.empty
  have hEA (A : Finset ι) (j : Fin L) : E A j ⊆ shadingAtom Y A := by
    dsimp [E]
    split_ifs
    · exact (hD A _).2.1
    · exact empty_subset _
  let C : Fin L → Set V := fun j => ⋃ A, E A j
  refine ⟨C, fun j => MeasurableSet.iUnion (fun A => hEm A j), ?_, ?_⟩
  · intro j j' hjj hγ
    apply Set.disjoint_left.mpr
    intro p hp hp'
    obtain ⟨A, hpA⟩ := mem_iUnion.mp hp
    obtain ⟨B, hpB⟩ := mem_iUnion.mp hp'
    have hAB : A = B := (shadingAtom_eq_pattern (hEA A j hpA)).trans
      (shadingAtom_eq_pattern (hEA B j' hpB)).symm
    subst B
    have hj : j ∈ A.image f := by
      by_contra h
      simpa only [E, ite_eq_right h, mem_empty_iff_false] using hpA
    have hj' : j' ∈ A.image f := by
      by_contra h
      simpa only [E, ite_eq_right h, mem_empty_iff_false] using hpB
    have hne : color A j ≠ color A j' :=
      fun he => hjj (hcolor A ⟨p, hEA A j hpA⟩ j hj j' hj' hγ he)
    exact Set.disjoint_left.mp (hDdisj A hne)
      (by simpa only [E, ite_eq_left hj] using hpA)
      (by simpa only [E, ite_eq_left hj'] using hpB)
  · intro i
    let F : Finset (Finset ι) := Finset.univ.filter fun A => i ∈ A
    have hcut : Y i ∩ C (f i) = ⋃ A ∈ F, D A (color A (f i)) := by
      ext p
      constructor
      · rintro ⟨hp, hpC⟩
        obtain ⟨A, hpA⟩ := mem_iUnion.mp hpC
        have hiA : i ∈ A := ((hEA A (f i) hpA).2 i).mp hp
        refine mem_iUnion₂.mpr ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiA⟩, ?_⟩
        simpa only [E, ite_eq_left (Finset.mem_image_of_mem f hiA)] using hpA
      · intro hp
        obtain ⟨A, hAF, hpA⟩ := mem_iUnion₂.mp hp
        have hiA : i ∈ A := (Finset.mem_filter.mp hAF).2
        have hpAtom := (hD A (color A (f i))).2.1 hpA
        refine ⟨(hpAtom.2 i).mpr hiA, mem_iUnion.mpr ⟨A, ?_⟩⟩
        simpa only [E, ite_eq_left (Finset.mem_image_of_mem f hiA)] using hpA
    have hfull : Y i = ⋃ A ∈ F, shadingAtom Y A := by
      ext p
      constructor
      · intro hp
        refine mem_iUnion₂.mpr ⟨shadingPattern Y p, ?_, mem_shadingAtom_pattern (mem_iUnion.mpr ⟨i, hp⟩)⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_shadingPattern Y p i).mpr hp⟩
      · intro hp
        obtain ⟨A, hAF, hpA⟩ := mem_iUnion₂.mp hp
        exact (hpA.2 i).mpr (Finset.mem_filter.mp hAF).2
    rw [hcut, measure_biUnion_finset, hfull, measure_biUnion_finset, Finset.mul_sum]
    · exact Finset.sum_congr rfl (fun A _ => (hD A _).2.2)
    · exact fun A _ B _ hAB => shadingAtom_disjoint Y hAB
    · exact fun A _ => shadingAtom_measurable hYm A
    · exact fun A _ B _ hAB => (shadingAtom_disjoint Y hAB).mono (hD A _).2.1 (hD B _).2.1
    · exact fun A _ => (hD A _).1

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
