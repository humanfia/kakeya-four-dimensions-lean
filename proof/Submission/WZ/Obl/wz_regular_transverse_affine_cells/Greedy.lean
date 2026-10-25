-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.Greedy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- One piece produced by the greedy container extraction. -/
structure ShadedCell (ι : Type*) where
  indices : Finset ι
  region : Set E
  shading : ι → Set E

def ShadedCell.support {ι : Type*} (C : ShadedCell ι) : Set E :=
  ⋃ i ∈ C.indices, C.shading i

/-- The geometry of the selected container is abstracted into `Good`; the shading
conditions retain the whole original set as their density reference. -/
def ShadedCell.Valid {ι : Type*} (C : ShadedCell ι) (F : Finset ι)
    (U Y : ι → Set E) (θ : ℝ≥0∞) (Good : Finset ι → Set E → Prop) : Prop :=
  C.indices.Nonempty ∧ C.indices ⊆ F ∧ Good C.indices C.region ∧
  (∀ i ∈ C.indices, U i ⊆ C.region) ∧
  (∀ i ∈ C.indices, MeasurableSet (C.shading i)) ∧
  (∀ i ∈ C.indices, C.shading i ⊆ Y i) ∧
  (∀ i ∈ C.indices, θ * volume (U i) ≤ volume (C.shading i))

lemma ShadedCell.support_subset_region {ι : Type*} {C : ShadedCell ι} {F : Finset ι}
    {U Y : ι → Set E} {θ : ℝ≥0∞} {Good : Finset ι → Set E → Prop}
    (hC : C.Valid F U Y θ Good) (hYU : ∀ i ∈ F, Y i ⊆ U i) : C.support ⊆ C.region := by
  intro p hp
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
  exact hC.2.2.2.1 i hi (hYU i (hC.2.1 hi) (hC.2.2.2.2.2.1 i hi hpi))

/-- A greedy extraction with a local overlap bound. Each step retains all the current
shading of the selected indices and removes its container from future shadings.
The result has disjoint physical supports and a global mass accounting inequality. -/
lemma greedy_container_extraction {ι : Type*} (U : ι → Set E)
    (Good : Finset ι → Set E → Prop) (L θ : ℝ≥0∞)
    (select : ∀ (F : Finset ι), F.Nonempty →
      ∃ (I : Finset ι) (W : Set E), I.Nonempty ∧ I ⊆ F ∧ MeasurableSet W ∧
        Good I W ∧ (∀ i ∈ I, U i ⊆ W) ∧
        ∑ i ∈ F, volume (U i ∩ W) ≤ L * ∑ i ∈ I, volume (U i))
    (F : Finset ι) (Y : ι → Set E)
    (hYm : ∀ i ∈ F, MeasurableSet (Y i)) (hYU : ∀ i ∈ F, Y i ⊆ U i)
    (hdense : ∀ i ∈ F, θ * volume (U i) ≤ volume (Y i)) :
    ∃ (m : ℕ) (C : Fin m → ShadedCell ι),
      (∀ j, (C j).Valid F U Y θ Good) ∧
      Pairwise (fun j k => Disjoint (C j).support (C k).support) ∧
      ∑ i ∈ F, volume (Y i) ≤ θ * ∑ i ∈ F, volume (U i) +
        L * ∑ j, ∑ i ∈ (C j).indices, volume (U i) := by
  classical
  induction F using Finset.strongInductionOn generalizing Y with
  | _ F ih =>
    rcases F.eq_empty_or_nonempty with rfl | hF
    · refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
      · intro j; exact j.elim0
      · intro j; exact j.elim0
      · simp
    obtain ⟨I, W, hI, hIF, hW, hGood, hUW, hover⟩ := select F hF
    let Y' : ι → Set E := fun i => Y i \ W
    let J : Finset ι := (F \ I).filter fun i => θ * volume (U i) ≤ volume (Y' i)
    have hJF : J ⊆ F := (Finset.filter_subset _ _).trans Finset.sdiff_subset
    have hJFI : J ⊆ F \ I := Finset.filter_subset _ _
    have hJstrict : J ⊂ F := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hJF, ?_⟩
      intro heq
      obtain ⟨i, hi⟩ := hI
      have hiJ : i ∈ J := heq.symm ▸ hIF hi
      exact (Finset.mem_sdiff.mp (hJFI hiJ)).2 hi
    have hY'm : ∀ i ∈ J, MeasurableSet (Y' i) := fun i hi => (hYm i (hJF hi)).diff hW
    have hY'U : ∀ i ∈ J, Y' i ⊆ U i := fun i hi => sdiff_subset.trans (hYU i (hJF hi))
    have hY'dense : ∀ i ∈ J, θ * volume (U i) ≤ volume (Y' i) :=
      fun i hi => (Finset.mem_filter.mp hi).2
    obtain ⟨m, C, hC, hCdisj, hCmass⟩ := ih J hJstrict Y' hY'm hY'U hY'dense
    let C₀ : ShadedCell ι := ⟨I, W, Y⟩
    let C' : Fin (m + 1) → ShadedCell ι := Fin.cases C₀ C
    have hC₀ : C₀.Valid F U Y θ Good :=
      ⟨hI, hIF, hGood, hUW, fun i hi => hYm i (hIF hi),
        fun _ _ => Subset.rfl, fun i hi => hdense i (hIF hi)⟩
    have hC' : ∀ j, (C' j).Valid F U Y θ Good := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact hC₀
      · obtain ⟨hn, hsub, hg, hreg, hm, hsh, hd⟩ := hC k
        exact ⟨hn, hsub.trans hJF, hg, hreg, hm, fun i hi => (hsh i hi).trans sdiff_subset, hd⟩
    have hCavoid : ∀ j, (C j).support ⊆ Wᶜ := by
      intro j p hp
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
      exact ((hC j).2.2.2.2.2.1 i hi hpi).2
    have hC₀disj : ∀ j, Disjoint C₀.support (C j).support := by
      intro j
      exact disjoint_compl_right.mono (ShadedCell.support_subset_region hC₀ hYU) (hCavoid j)
    refine ⟨m + 1, C', hC', ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j' => ?_) j
      · intro k
        refine Fin.cases ?_ (fun k' => ?_) k
        · intro hjk
          exact False.elim (hjk rfl)
        · intro _
          exact hC₀disj k'
      · intro k
        refine Fin.cases ?_ (fun k' => ?_) k
        · intro _
          exact (hC₀disj j').symm
        · intro hjk
          exact hCdisj (fun h => hjk (congrArg Fin.succ h))
    · have hlow : ∀ i ∈ F \ J, volume (Y' i) ≤ θ * volume (U i) := by
        intro i hi
        obtain ⟨hiF, hiJ⟩ := Finset.mem_sdiff.mp hi
        by_cases hiI : i ∈ I
        · have heq : Y' i = ∅ := sdiff_eq_empty.mpr ((hYU i hiF).trans (hUW i hiI))
          rw [heq, measure_empty]
          exact zero_le
        · exact le_of_not_ge (fun h => hiJ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hiF, hiI⟩, h⟩))
      have hsplit : ∑ i ∈ F, volume (Y i) =
          (∑ i ∈ F, volume (Y' i)) + ∑ i ∈ F, volume (Y i ∩ W) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact (measure_sdiff_add_inter (Y i) hW).symm
      have hpart : (∑ i ∈ F, volume (Y' i)) =
          (∑ i ∈ J, volume (Y' i)) + ∑ i ∈ F \ J, volume (Y' i) := by
        simpa only [add_comm] using (Finset.sum_sdiff (f := fun i => volume (Y' i)) hJF).symm
      have hweights : (∑ i ∈ J, volume (U i)) + (∑ i ∈ F \ J, volume (U i)) =
          ∑ i ∈ F, volume (U i) := by
        simpa only [add_comm] using Finset.sum_sdiff (f := fun i => volume (U i)) hJF
      have hsmall : (∑ i ∈ F \ J, volume (Y' i)) ≤ θ * ∑ i ∈ F \ J, volume (U i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hlow
      have hover' : (∑ i ∈ F, volume (Y i ∩ W)) ≤ L * ∑ i ∈ I, volume (U i) := by
        apply le_trans _ hover
        exact Finset.sum_le_sum fun i hi => measure_mono (inter_subset_inter_left W (hYU i hi))
      calc ∑ i ∈ F, volume (Y i)
          = ((∑ i ∈ J, volume (Y' i)) + ∑ i ∈ F \ J, volume (Y' i)) +
              ∑ i ∈ F, volume (Y i ∩ W) := by rw [hsplit, hpart]
        _ ≤ ((θ * ∑ i ∈ J, volume (U i) + L * ∑ j, ∑ i ∈ (C j).indices, volume (U i)) +
              θ * ∑ i ∈ F \ J, volume (U i)) + L * ∑ i ∈ I, volume (U i) :=
          add_le_add (add_le_add hCmass hsmall) hover'
        _ = θ * ∑ i ∈ F, volume (U i) + L * ∑ j, ∑ i ∈ (C' j).indices, volume (U i) := by
          rw [← hweights, Fin.sum_univ_succ]
          simp only [C', C₀, Fin.cases_zero, Fin.cases_succ]
          ring

/-- Starting at twice the deletion threshold gives a lower bound for the total
weight assigned to the disjoint extracted cells. -/
lemma greedy_container_retained_weight {ι : Type*} (U : ι → Set E)
    (Good : Finset ι → Set E → Prop) (L θ : ℝ≥0∞) (hθfin : θ ≠ ∞)
    (select : ∀ (F : Finset ι), F.Nonempty →
      ∃ (I : Finset ι) (W : Set E), I.Nonempty ∧ I ⊆ F ∧ MeasurableSet W ∧
        Good I W ∧ (∀ i ∈ I, U i ⊆ W) ∧
        ∑ i ∈ F, volume (U i ∩ W) ≤ L * ∑ i ∈ I, volume (U i))
    (F : Finset ι) (Y : ι → Set E)
    (hYm : ∀ i ∈ F, MeasurableSet (Y i)) (hYU : ∀ i ∈ F, Y i ⊆ U i)
    (hUfin : ∀ i ∈ F, volume (U i) ≠ ∞)
    (hdense : ∀ i ∈ F, (2 * θ) * volume (U i) ≤ volume (Y i)) :
    ∃ (m : ℕ) (C : Fin m → ShadedCell ι),
      (∀ j, (C j).Valid F U Y θ Good) ∧
      Pairwise (fun j k => Disjoint (C j).support (C k).support) ∧
      θ * ∑ i ∈ F, volume (U i) ≤ L * ∑ j, ∑ i ∈ (C j).indices, volume (U i) := by
  have hθ : θ ≤ 2 * θ := by rw [two_mul]; exact le_self_add
  have hdense' : ∀ i ∈ F, θ * volume (U i) ≤ volume (Y i) :=
    fun i hi => (mul_le_mul_left hθ _).trans (hdense i hi)
  obtain ⟨m, C, hC, hdisj, hmass⟩ :=
    greedy_container_extraction U Good L θ select F Y hYm hYU hdense'
  refine ⟨m, C, hC, hdisj, ?_⟩
  have hinit : (2 * θ) * ∑ i ∈ F, volume (U i) ≤ ∑ i ∈ F, volume (Y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hdense
  have hfin : θ * ∑ i ∈ F, volume (U i) ≠ ∞ := by
    apply ENNReal.mul_ne_top hθfin
    exact ENNReal.sum_ne_top.mpr hUfin
  apply ENNReal.le_of_add_le_add_left hfin
  calc θ * ∑ i ∈ F, volume (U i) + θ * ∑ i ∈ F, volume (U i)
      = (2 * θ) * ∑ i ∈ F, volume (U i) := by ring
    _ ≤ ∑ i ∈ F, volume (Y i) := hinit
    _ ≤ _ := hmass

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
