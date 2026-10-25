-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.SeparatedRelative.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.SeparatedCellRows
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalPartition
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.RelativeCap

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set
open WangZahlLot.Obl.wz_extremal_lipschitz_grains
open scoped Classical

set_option maxHeartbeats 800000 in
/-- Separate each tube's occupied cells and then restore a pointwise fraction
of the original incidence. Angular broadness can therefore be transferred to
this refinement without losing the separation needed for global prism glue. -/
theorem separated_relative_shading {δ r τ L : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r) (hτ : 0 < τ)
    {n N : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (C : Fin N → Set Space) (q : Fin N → Space)
    (hv : ∀ i, ‖v i‖ = 1) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, volume (Y i) ≠ ⊤) (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hC : ∀ j, MeasurableSet (C j)) (hCball : ∀ j, C j ⊆ Metric.ball (q j) r)
    (hdisj : Pairwise fun j k => Disjoint (C j) (C k))
    (hcover : (⋃ i, Y i) ⊆ ⋃ j, C j)
    (hcross : ∀ i, ({j | (Y i ∩ C j).Nonempty}.ncard : ℝ) ≤ L)
    (hbudget : (τ * δ ^ 2 * r) * n * L ≤ (1 / 2 : ℝ) * shadingMass Y) :
    ∃ V : Fin n → Set Space,
      (∀ i, MeasurableSet (V i) ∧ V i ⊆ Y i) ∧
      shadingMass Y ≤ (4 * (⌈422400 / τ⌉₊ : ℝ)) * shadingMass V ∧
      (∀ p ∈ ⋃ i, V i, (1 / (4 * (⌈422400 / τ⌉₊ : ℝ))) * incidence Y p ≤ incidence V p) ∧
      (∀ i j k, j ≠ k → (V i ∩ C j).Nonempty → (V i ∩ C k).Nonempty →
        10 * r < dist (q j) (q k)) ∧
      (∀ i, (⋃ j, V i ∩ C j) = V i) ∧
      (∀ i, ({j | (V i ∩ C j).Nonempty}.ncard : ℝ) ≤ L) := by
  have hcellfin (j : Fin N) (i : Fin n) : volume (Y i ∩ C j) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin i) (measure_mono inter_subset_left)
  have htotal : (∑ j, ∑ i, (volume (Y i ∩ C j)).toReal) = shadingMass Y :=
    shading_mass_partition_real volume Y C hY hfin hC hdisj hcover
  obtain ⟨U, hU, _, hsep, hkeep⟩ := separated_dense_cell_refinement hδ hr hδr hτ x v
    (fun j i => Y i ∩ C j) q hv (fun j i => (hY i).inter (hC j)) hcellfin
    (fun j i _ hp => ⟨hYT i hp.1, hCball j hp.2⟩)
    (fun _ _ _ hjk => (hdisj hjk).mono inter_subset_right inter_subset_right)
    hcross (by simpa only [htotal] using hbudget)
  let W : Fin n → Set Space := fun i => ⋃ j, U j i
  have hW (i : Fin n) : MeasurableSet (W i) ∧ W i ⊆ Y i :=
    ⟨MeasurableSet.iUnion (fun j => (hU j i).1), iUnion_subset (fun j => (hU j i).2.trans inter_subset_left)⟩
  have hUfin (j : Fin N) (i : Fin n) : volume (U j i) ≠ ⊤ :=
    ne_top_of_le_ne_top (hcellfin j i) (measure_mono (hU j i).2)
  have hmeasure (i : Fin n) : volume (W i) = ∑ j, volume (U j i) := by
    have hh := measure_iUnion (fun j k hjk => (hdisj hjk).mono
      ((hU j i).2.trans inter_subset_right) ((hU k i).2.trans inter_subset_right))
      (fun j => (hU j i).1) (μ := volume)
    rw [tsum_fintype] at hh
    exact hh
  have hWmass : shadingMass W = ∑ j, ∑ i, (volume (U j i)).toReal := by
    unfold shadingMass
    simp_rw [hmeasure, ENNReal.toReal_sum (fun j _ => hUfin j _)]
    exact Finset.sum_comm
  have hkeepW : shadingMass Y ≤ (2 * (⌈422400 / τ⌉₊ : ℝ)) * shadingMass W := by
    simpa only [htotal, ← hWmass] using hkeep
  have hD : (0 : ℝ) < (⌈422400 / τ⌉₊ : ℝ) := by
    exact_mod_cast (Nat.ceil_pos.mpr (show 0 < 422400 / τ by positivity))
  obtain ⟨V, hV, hmass, hrelative⟩ := relative_incidence_refinement hY
    (fun i => (hW i).1) hfin (fun i => (hW i).2)
    (by positivity : 0 ≤ 1 / (4 * (⌈422400 / τ⌉₊ : ℝ)))
  have hVC (i : Fin n) (j : Fin N) : V i ∩ C j ⊆ U j i := by
    intro p hp
    have hpW := (hV i).2 hp.1
    obtain ⟨k, hpk⟩ := mem_iUnion.mp hpW
    by_cases hkj : k = j
    · exact hkj ▸ hpk
    · exact False.elim ((Set.disjoint_left.mp (hdisj hkj)) ((hU k i).2 hpk).2 hp.2)
  refine ⟨V, fun i => ⟨(hV i).1, (hV i).2.trans (hW i).2⟩, ?_, hrelative, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 4 * (⌈422400 / τ⌉₊ : ℝ))
    rw [mul_sub] at hh
    have he : (4 * (⌈422400 / τ⌉₊ : ℝ)) *
        (1 / (4 * (⌈422400 / τ⌉₊ : ℝ)) * shadingMass Y) = shadingMass Y := by field_simp
    rw [he] at hh
    nlinarith [hkeepW]
  · intro i j k hjk hj hk
    exact hsep i j k hjk (hj.mono (hVC i j)) (hk.mono (hVC i k))
  · intro i
    rw [← inter_iUnion]
    exact inter_eq_left.mpr (((hV i).2.trans (hW i).2).trans ((subset_iUnion Y i).trans hcover))
  · intro i
    have hh : ({j | (V i ∩ C j).Nonempty}.ncard : ℝ) ≤ {j | (Y i ∩ C j).Nonempty}.ncard := by
      exact_mod_cast ncard_le_ncard (fun j (hj : (V i ∩ C j).Nonempty) =>
        hj.mono (inter_subset_inter_left _ ((hV i).2.trans (hW i).2)))
    exact hh.trans (hcross i)

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
