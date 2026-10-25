-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.AngularPartition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AngularGeometry
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PartitionRefinement
import Submission.WZ.Obl.wz_measurable_angular_selection

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_balanced_cluster_cover

/-- Choose a measurable incident index whenever any shading is present. -/
lemma exists_measurable_incident_index {n : ℕ} (hn : 0 < n)
    (Y : Fin n → Set E) (hYm : ∀ i, MeasurableSet (Y i)) :
    ∃ a : E → Fin n, (∀ i, MeasurableSet {p | a p = i}) ∧
      ∀ p, (∃ i, p ∈ Y i) → p ∈ Y (a p) := by
  classical
  let S : E → Finset (Fin n) := fun p => Finset.univ.filter fun i => p ∈ Y i
  have hS : ∀ p i, i ∈ S p ↔ p ∈ Y i := by intro p i; simp [S]
  let select : Finset (Fin n) → Fin n := fun T => if h : T.Nonempty then h.choose else ⟨0, hn⟩
  have hselect : ∀ T : Finset (Fin n), T.Nonempty → select T ∈ T := by
    intro T hT
    simp only [select, dite_eq_left hT]
    exact hT.choose_spec
  refine ⟨fun p => select (S p), ?_, ?_⟩
  · intro i
    exact WangZahlLot.Obl.wz_measurable_angular_selection.measurableSet_pattern
      hYm S hS (fun T => select T = i)
  · intro p hp
    apply (hS p _).mp
    apply hselect
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, (hS p i).mpr hi⟩

namespace Angular

lemma measurable_label_fiber {n : ℕ} (θ : ℝ) (v : Fin n → E) (a : E → Fin n)
    (ha : ∀ i, MeasurableSet {p | a p = i}) (ℓ : Label) :
    MeasurableSet {p | label θ (v (a p)) p = ℓ} := by
  have hf (i : Fin n) : MeasurableSet {p : E | label θ (v i) p = ℓ} := by
    obtain ⟨L, k⟩ := ℓ
    simp only [label, Sigma.mk.inj_iff, heq_eq_eq]
    by_cases h : cell θ (v i) = L
    · simp only [h, true_and]
      have hm : Measurable (fun p : E => ⌊inner ℝ (W θ L) p / θ⌋) := by
        apply Measurable.floor
        apply Continuous.measurable
        fun_prop
      exact hm (measurableSet_singleton k)
    · simpa only [h, false_and, ofPred_false] using MeasurableSet.empty
  have he : {p | label θ (v (a p)) p = ℓ} =
      ⋃ i : Fin n, ({p | a p = i} ∩ {p | label θ (v i) p = ℓ}) := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨a p, rfl, h⟩
    · rintro ⟨i, hi, hp⟩
      simpa only [hi] using hp
  rw [he]
  exact MeasurableSet.iUnion fun i => (ha i).inter (hf i)

open Classical in
/-- Tangentially intersecting thin sets carry disjoint measurable point labels.
Each set meets at most 2304 labels, and each met label supplies a whole-set slab
container of width `9*θ`. -/
lemma slab_partition {n : ℕ} (hn : 0 < n) {a θ : ℝ} (hθ : 0 < θ) (ha : a ≤ θ)
    (U Y : Fin n → Set E) (u c : Fin n → E)
    (hUne : ∀ i, (U i).Nonempty) (hu : ∀ i, ‖u i‖ = 1)
    (hbound : ∀ i, U i ⊆ Metric.closedBall (0 : E) 1)
    (hthin : ∀ i q, q ∈ U i → |inner ℝ (u i) (q - c i)| ≤ a)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYU : ∀ i, Y i ⊆ U i)
    (htangent : ∀ p i j, p ∈ Y i → p ∈ Y j → min ‖u i - u j‖ ‖u i + u j‖ ≤ θ) :
    ∃ (F : Finset Label) (B : Label → Set E),
      (∀ ℓ, MeasurableSet (B ℓ)) ∧ Pairwise (fun ℓ ℓ' => Disjoint (B ℓ) (B ℓ')) ∧
      (∀ i, Y i ⊆ ⋃ ℓ ∈ F, B ℓ) ∧
      (∀ i, (F.filter (fun ℓ => (Y i ∩ B ℓ).Nonempty)).card ≤ 2304) ∧
      (∀ i ℓ, (Y i ∩ B ℓ).Nonempty → ‖W θ ℓ.1‖ = 1 ∧
        U i ⊆ slab (innerSL ℝ (W θ ℓ.1)) (θ * ℓ.2) (9 * θ)) := by
  classical
  choose p₀ hp₀ using hUne
  obtain ⟨select, hselectm, hselect⟩ := exists_measurable_incident_index hn Y hYm
  let B : Label → Set E := fun ℓ => {p | label θ (u (select p)) p = ℓ}
  let F : Finset Label := Finset.univ.biUnion fun i => possibleLabels θ (u i) (p₀ i)
  have hlabel (i : Fin n) (p : E) (hp : p ∈ Y i) :
      label θ (u (select p)) p ∈ possibleLabels θ (u i) (p₀ i) := by
    exact label_mem_possible hθ ha (hu _) (hbound i) (hthin i) (hp₀ i)
      (hYU i hp) (htangent p i (select p) hp (hselect p ⟨i, hp⟩))
  refine ⟨F, B, fun ℓ => measurable_label_fiber θ u select hselectm ℓ, ?_, ?_, ?_, ?_⟩
  · intro ℓ ℓ' hne
    rw [Set.disjoint_left]
    intro p hp hp'
    exact hne (hp.symm.trans hp')
  · intro i p hp
    apply mem_iUnion₂.mpr
    exact ⟨label θ (u (select p)) p,
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hlabel i p hp⟩, rfl⟩
  · intro i
    apply le_trans _ (card_possibleLabels hθ (u i) (p₀ i))
    apply Finset.card_le_card
    intro ℓ hℓ
    obtain ⟨p, hp, hpℓ⟩ := (Finset.mem_filter.mp hℓ).2
    exact hpℓ ▸ hlabel i p hp
  · intro i ℓ hmeet
    obtain ⟨p, hp, hpℓ⟩ := hmeet
    have hsel := hselect p ⟨i, hp⟩
    have hW := W_spec (hu (select p)) (rfl : cell θ (u (select p)) = cell θ (u (select p)))
    have hcontains := label_slab_contains hθ ha (hu _) (hbound i) (hthin i)
      (hYU i hp) (htangent p i (select p) hp hsel)
    change label θ (u (select p)) p = ℓ at hpℓ
    rw [hpℓ] at hcontains
    refine ⟨?_, hcontains⟩
    have he := congrArg Sigma.fst hpℓ
    change cell θ (u (select p)) = ℓ.1 at he
    simpa only [he] using hW.1

/-- The angular decomposition with a fixed density threshold in each retained
slab piece. The total discarded shading mass costs at most 2304 thresholds. -/
lemma slab_refinement {n : ℕ} (hn : 0 < n) {a θ : ℝ} (hθ : 0 < θ) (ha : a ≤ θ)
    (U Y : Fin n → Set E) (u c : Fin n → E)
    (hUne : ∀ i, (U i).Nonempty) (hu : ∀ i, ‖u i‖ = 1)
    (hbound : ∀ i, U i ⊆ Metric.closedBall (0 : E) 1)
    (hthin : ∀ i q, q ∈ U i → |inner ℝ (u i) (q - c i)| ≤ a)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYU : ∀ i, Y i ⊆ U i)
    (htangent : ∀ p i j, p ∈ Y i → p ∈ Y j → min ‖u i - u j‖ ‖u i + u j‖ ≤ θ)
    (τ : ℝ≥0∞) :
    ∃ (F : Finset Label) (B : Label → Set E) (H : Fin n → Set E),
      (∀ ℓ, MeasurableSet (B ℓ)) ∧ Pairwise (fun ℓ ℓ' => Disjoint (B ℓ) (B ℓ')) ∧
      (∀ i, MeasurableSet (H i)) ∧ (∀ i, H i ⊆ Y i) ∧
      (∀ i, H i ⊆ ⋃ ℓ ∈ F, B ℓ) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (H i)) + 2304 * τ * ∑ i, volume (U i) ∧
      (∀ i ℓ, ℓ ∈ F → (H i ∩ B ℓ).Nonempty →
        τ * volume (U i) ≤ volume (H i ∩ B ℓ)) ∧
      (∀ i ℓ, (H i ∩ B ℓ).Nonempty → ‖W θ ℓ.1‖ = 1 ∧
        U i ⊆ slab (innerSL ℝ (W θ ℓ.1)) (θ * ℓ.2) (9 * θ)) := by
  obtain ⟨F, B, hBm, hBdisj, hcover, hcount, hwhole⟩ :=
    slab_partition hn hθ ha U Y u c hUne hu hbound hthin hYm hYU htangent
  obtain ⟨H, hHm, hHY, hmass, hreg⟩ := bounded_partition_density_refinement volume U Y hYm
    F B (fun ℓ _ => hBm ℓ) 2304 hcount τ
  refine ⟨F, B, H, hBm, hBdisj, hHm, hHY, fun i => (hHY i).trans (hcover i),
    by simpa only [Nat.cast_ofNat] using hmass, hreg, ?_⟩
  intro i ℓ hmeet
  exact hwhole i ℓ (hmeet.mono (inter_subset_inter_left _ (hHY i)))

end Angular
end WangZahlLot.Obl.wz_regular_transverse_affine_cells
