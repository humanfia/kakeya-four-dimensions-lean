-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.WeakPlane.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CompactIncidence
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.PlaneSelection

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped Classical ENNReal

theorem exists_shadingAtom {n : ℕ} (Y : Fin n → Set Space) {p : Space}
    (hp : p ∈ ⋃ i, Y i) : ∃ s : Finset (Fin n), p ∈ shadingAtom Y s := by
  refine ⟨Finset.univ.filter (fun i => p ∈ Y i), hp, ?_⟩
  simp

theorem shadingAtom_eq_of_mem {n : ℕ} {Y : Fin n → Set Space}
    {p : Space} {s t : Finset (Fin n)} (hs : p ∈ shadingAtom Y s)
    (ht : p ∈ shadingAtom Y t) : s = t := by
  ext i
  exact (hs.2 i).symm.trans (ht.2 i)

/-- Atomwise finite selection gives a measurable plane map and retains at least half
the total shading mass. Its two counting hypotheses must come from the geometric
transversality and multilinear estimates. No regularity of the resulting map is asserted. -/
theorem measurable_plane_selection {n : ℕ} (Y : Fin n → Set Space) (v : Fin n → Space)
    (hY : ∀ i, MeasurableSet (Y i)) (hUfin : volume (⋃ i, Y i) ≠ ∞)
    {b τ : ℝ} (hb : 0 < b)
    (hpairs : ∀ s : Finset (Fin n), (shadingAtom Y s).Nonempty →
      (s.card : ℝ) ^ 2 ≤
        2 * (((s.product s).filter fun ij => b ≤ ‖cross (v ij.1) (v ij.2)‖).card : ℝ))
    (htriples : ∀ s : Finset (Fin n), (shadingAtom Y s).Nonempty →
      (∑ i ∈ s, ∑ j ∈ s,
        ((s.filter fun k => τ < |inner ℝ (v k) (cross (v i) (v j))|).card : ℝ)) ≤
          (s.card : ℝ) ^ 3 / 4) :
    ∃ (Z : Fin n → Set Space) (P : Space → Space),
      (∀ i, Z i ⊆ Y i) ∧ (∀ i, MeasurableSet (Z i)) ∧
      shadingMass Y / 2 ≤ shadingMass Z ∧ Measurable P ∧
      (∀ p ∈ ⋃ i, Z i, ‖P p‖ = 1) ∧
      (∀ i p, p ∈ Z i → |inner ℝ (v i) (P p)| ≤ τ / b) := by
  have hsel : ∀ s : Finset (Fin n), ∃ (F : Finset (Fin n)) (N : Space),
      F ⊆ s ∧ ((shadingAtom Y s).Nonempty →
        (s.card : ℝ) / 2 ≤ (F.card : ℝ) ∧ ‖N‖ = 1 ∧
          ∀ k ∈ F, |inner ℝ (v k) N| ≤ τ / b) := by
    intro s
    by_cases hs : (shadingAtom Y s).Nonempty
    · have hsn : s.Nonempty := by
        obtain ⟨p, hp⟩ := hs
        obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1
        exact ⟨i, (hp.2 i).mp hi⟩
      obtain ⟨F, N, hF, hcard, hN, hinner⟩ :=
        narrow_plane_selection s v hsn hb (hpairs s hs) (htriples s hs)
      exact ⟨F, N, hF, fun _ => ⟨hcard, hN, hinner⟩⟩
    · exact ⟨∅, 0, Finset.empty_subset _, fun h => (hs h).elim⟩
  choose F N hFs hprops using hsel
  let Z : Fin n → Set Space := fun i =>
    ⋃ s : Finset (Fin n), if i ∈ F s then shadingAtom Y s else ∅
  let P : Space → Space := fun p =>
    ∑ s : Finset (Fin n), (shadingAtom Y s).indicator (fun _ => N s) p
  have hP : Measurable P := Finset.measurable_sum _ fun s _ =>
    measurable_const.indicator (measurableSet_shadingAtom hY s)
  have hZY : ∀ i, Z i ⊆ Y i := by
    intro i p hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    split_ifs at hs with hi
    · exact (hs.2 i).mpr (hFs s hi)
    · exact hs.elim
  have hZm : ∀ i, MeasurableSet (Z i) := by
    intro i
    apply MeasurableSet.iUnion
    intro s
    split_ifs
    · exact measurableSet_shadingAtom hY s
    · exact MeasurableSet.empty
  have hZatom : ∀ {s : Finset (Fin n)} {p : Space}, p ∈ shadingAtom Y s →
      ∀ i, p ∈ Z i ↔ i ∈ F s := by
    intro s p hp i
    constructor
    · intro hpi
      obtain ⟨t, ht⟩ := mem_iUnion.mp hpi
      split_ifs at ht with hit
      · have hts := shadingAtom_eq_of_mem ht hp
        simpa only [hts] using hit
      · exact ht.elim
    · intro hi
      exact mem_iUnion.mpr ⟨s, by simpa only [ite_eq_left hi] using hp⟩
  have hPatom : ∀ {s : Finset (Fin n)} {p : Space}, p ∈ shadingAtom Y s → P p = N s := by
    intro s p hp
    dsimp [P]
    rw [Finset.sum_eq_single s]
    · exact Set.indicator_of_mem hp _
    · intro t _ hts
      apply Set.indicator_of_notMem
      intro ht
      exact hts (shadingAtom_eq_of_mem ht hp)
    · simp
  have hhalf : ∀ p, incidence Y p / 2 ≤ incidence Z p := by
    intro p
    by_cases hp : p ∈ ⋃ i, Y i
    · obtain ⟨s, hs⟩ := exists_shadingAtom Y hp
      have hYcard : incidence Y p = (s.card : ℝ) := by
        rw [incidence_eq_ncard]
        have he : {i | p ∈ Y i} = (s : Set (Fin n)) := by
          ext i; exact hs.2 i
        rw [he, Set.ncard_coe_finset]
      have hZcard : incidence Z p = ((F s).card : ℝ) := by
        rw [incidence_eq_ncard]
        have he : {i | p ∈ Z i} = (F s : Set (Fin n)) := by
          ext i; exact hZatom hs i
        rw [he, Set.ncard_coe_finset]
      rw [hYcard, hZcard]
      exact (hprops s ⟨p, hs⟩).1
    · rw [incidence_eq_zero_of_notMem Y hp, zero_div]
      exact incidence_nonneg Z p
  have hYfin : ∀ i, volume (Y i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hUfin (measure_mono (subset_iUnion Y i))
  have hZfin : ∀ i, volume (Z i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top (hYfin i) (measure_mono (hZY i))
  have hmass : shadingMass Y / 2 ≤ shadingMass Z := by
    have h := integral_mono ((integrable_incidence hY hYfin).div_const 2)
      (integrable_incidence hZm hZfin) hhalf
    rwa [integral_div, integral_incidence hY hYfin, integral_incidence hZm hZfin] at h
  refine ⟨Z, P, hZY, hZm, hmass, hP, ?_, ?_⟩
  · intro p hp
    obtain ⟨s, hs⟩ := exists_shadingAtom Y ((iUnion_mono hZY) hp)
    rw [hPatom hs]
    exact (hprops s ⟨p, hs⟩).2.1
  · intro i p hp
    obtain ⟨s, hs⟩ := exists_shadingAtom Y (mem_iUnion.mpr ⟨i, hZY i hp⟩)
    rw [hPatom hs]
    exact (hprops s ⟨p, hs⟩).2.2 i ((hZatom hs i).mp hp)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
