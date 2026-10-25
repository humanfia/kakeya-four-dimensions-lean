-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.NarrowWindowBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.SlopeBands
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.NarrowLocalization
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.LocalizationParameters

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open Set MeasureTheory
open WangZahlLot.Obl.wz_jet_close_pair_moment

/-- The coefficient-dependent slope threshold is at most the common
window cap `2 κ D`. -/
theorem localized_narrow_union_subset_window {n : ℕ}
    (A B : Finset (Fin n)) (q : Fin n → EuclideanSpace ℝ (Fin 3))
    (g : Fin n → ℝ → ℝ) {δ κ D l u : ℝ} (hκ : 0 ≤ κ)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, dist (q i) (q j) ≤ 2*D) :
    ((⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
      {p : ℝ × ℝ | p.2 ∈ Icc l u}) ⊆ narrowWindowUnion A B g δ l u (2*κ*D) := by
  intro p hp
  obtain ⟨i, hi, hp'⟩ := mem_iUnion₂.mp hp.1
  obtain ⟨j, hj, hp'⟩ := mem_iUnion₂.mp hp'
  refine mem_iUnion₂.mpr ⟨i,hi,mem_iUnion₂.mpr ⟨j,hj,hp'.1.1,hp'.1.2,hp.2,?_⟩⟩
  exact hp'.2.trans_le (by nlinarith [mul_le_mul_of_nonneg_left (hcross i hi j hj) hκ])

/-- A local estimate supplied under uniform curvature ordering applies to
every nonempty refined window; empty windows contribute zero. -/
theorem volume_localized_narrow_union_le_of_oriented_window {n : ℕ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hjet : JetControlled q g)
    (A B : Finset (Fin n)) {δ D κ l u V : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 < D) (hnatural : Real.sqrt (δ/D) ≤ κ)
    (hκ : κ < 1/100000) (hl : -1 ≤ l) (hu : u ≤ 1) (hshort : u-l ≤ 1/10000)
    (hA : ∀ i ∈ A, ∀ j ∈ A, dist (q i) (q j) ≤ D/10000)
    (hB : ∀ i ∈ B, ∀ j ∈ B, dist (q i) (q j) ≤ D/10000)
    (hcross : ∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j) ∧ dist (q i) (q j) ≤ 2*D)
    (hbound : ((∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
        D/120 ≤ deriv (deriv (g i)) t-deriv (deriv (g j)) t) ∨
      (∀ i ∈ A, ∀ j ∈ B, ∀ t ∈ Icc l u,
        D/120 ≤ deriv (deriv (g j)) t-deriv (deriv (g i)) t)) →
      volume (narrowWindowUnion A B g δ l u (2*κ*D)) ≤ ENNReal.ofReal V) :
    volume ((⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
      {p : ℝ × ℝ | p.2 ∈ Icc l u}) ≤ ENNReal.ofReal V := by
  classical
  let E := ((⋃ i ∈ A, ⋃ j ∈ B, narrowIntersection δ κ (q i) (q j) (g i) (g j)) ∩
      {p : ℝ × ℝ | p.2 ∈ Icc l u})
  change volume E ≤ _
  rcases E.eq_empty_or_nonempty with he | he
  · rw [he, measure_empty]
    exact zero_le
  · have hord := curvature_order_of_narrow_union_nonempty hg hjet A B hδ hD hnatural
      hκ hl hu hshort hA hB hcross he
    exact (measure_mono (localized_narrow_union_subset_window A B q g
      ((Real.sqrt_nonneg _).trans hnatural) (fun i hi j hj => (hcross i hi j hj).2))).trans (hbound hord)

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
