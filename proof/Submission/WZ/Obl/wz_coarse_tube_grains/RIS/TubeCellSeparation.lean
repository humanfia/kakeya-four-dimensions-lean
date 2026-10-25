-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.TubeCellSeparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.LocalNormalize
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.WeightedSelection

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped Classical ENNReal

/-- A local tube segment has volume bounded by its cross-sectional area times
the ball radius. The constant is uniform even at the ends of the segment. -/
theorem local_tube_volume_upper {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hδr : δ ≤ r)
    (x v c : Space) (hv : ‖v‖ = 1) :
    volume (Tube δ x v ∩ ball c r) ≤ ENNReal.ofReal (38400 * δ ^ 2 * r) := by
  by_cases hne : (Tube δ x v ∩ ball c r).Nonempty
  · obtain ⟨z, _, hsub⟩ := local_tube_carrier hr hδr x v c hv hne
    have hρ : 0 < δ / (100 * r) := by positivity
    have hρ1 : δ / (100 * r) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    have hh := (measure_mono hsub).trans (tube_volume_upper hρ hρ1 z v hv)
    rw [localMap_volume] at hh
    have hf : 0 < (100 * r)⁻¹ ^ 3 := by positivity
    apply (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr hf)) ENNReal.ofReal_ne_top).mp
    calc
      ENNReal.ofReal ((100 * r)⁻¹ ^ 3) * volume (Tube δ x v ∩ ball c r) ≤
          ENNReal.ofReal (384 * (δ / (100 * r)) ^ 2) := hh
      _ = ENNReal.ofReal ((100 * r)⁻¹ ^ 3) * ENNReal.ofReal (38400 * δ ^ 2 * r) := by
        rw [← ENNReal.ofReal_mul hf.le]
        congr 1
        field_simp
        <;> ring
  · rw [not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact bot_le

/-- There are few nearby disjoint dense pieces of a single tube. -/
theorem nearby_tube_cells_count {δ r τ : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hδr : δ ≤ r) (hτ : 0 < τ) {N : ℕ}
    (x v : Space) (hv : ‖v‖ = 1) (Y : Fin N → Set Space) (q : Fin N → Space)
    (hY : ∀ j, MeasurableSet (Y j))
    (hYT : ∀ j, Y j ⊆ Tube δ x v ∩ ball (q j) r)
    (hdisj : Pairwise fun j k => Disjoint (Y j) (Y k))
    (hdense : ∀ j, (Y j).Nonempty → ENNReal.ofReal (τ * δ ^ 2 * r) ≤ volume (Y j))
    (p : Space) :
    ((Finset.univ.filter fun j => (Y j).Nonempty ∧ dist (q j) p ≤ 10 * r).card : ℝ) ≤ 422400 / τ := by
  let A := Finset.univ.filter fun j => (Y j).Nonempty ∧ dist (q j) p ≤ 10 * r
  have hsub : (⋃ j ∈ A, Y j) ⊆ Tube δ x v ∩ ball p (11 * r) := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hz
    have hz' := hYT j hzj
    refine ⟨hz'.1, ?_⟩
    have hdist := (Finset.mem_filter.mp hj).2.2
    have hzq : dist z (q j) < r := hz'.2
    have ht := dist_triangle z (q j) p
    change dist z p < 11 * r
    linarith
  have hAdisj : (↑A : Set (Fin N)).PairwiseDisjoint Y :=
    fun _ _ _ _ hjk => hdisj hjk
  have hmass : ENNReal.ofReal ((A.card : ℝ) * (τ * δ ^ 2 * r)) ≤
      ENNReal.ofReal (422400 * δ ^ 2 * r) := by
    calc
      _ = ∑ _j ∈ A, ENNReal.ofReal (τ * δ ^ 2 * r) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
      _ ≤ ∑ j ∈ A, volume (Y j) :=
        Finset.sum_le_sum (fun j hj => hdense j (Finset.mem_filter.mp hj).2.1)
      _ = volume (⋃ j ∈ A, Y j) := (measure_biUnion_finset hAdisj (fun j _ => hY j)).symm
      _ ≤ volume (Tube δ x v ∩ ball p (11 * r)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (38400 * δ ^ 2 * (11 * r)) :=
        local_tube_volume_upper hδ (by positivity) (by linarith) x v p hv
      _ = _ := by congr 1; ring
  have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 422400 * δ ^ 2 * r)).mp hmass
  apply (le_div_iff₀ hτ).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < δ ^ 2 * r)).mp
  nlinarith [hh]

/-- Select separated local pieces for one tube, retaining a reciprocal-degree
share of their shading mass. The separation concerns only that tube's pieces. -/
theorem tube_cell_separated_subfamily {δ r τ : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hδr : δ ≤ r) (hτ : 0 < τ) {N : ℕ}
    (x v : Space) (hv : ‖v‖ = 1) (Y : Fin N → Set Space) (q : Fin N → Space)
    (hY : ∀ j, MeasurableSet (Y j))
    (hYT : ∀ j, Y j ⊆ Tube δ x v ∩ ball (q j) r)
    (hdisj : Pairwise fun j k => Disjoint (Y j) (Y k))
    (hdense : ∀ j, (Y j).Nonempty → ENNReal.ofReal (τ * δ ^ 2 * r) ≤ volume (Y j)) :
    ∃ S : Finset (Fin N), (∀ j ∈ S, (Y j).Nonempty) ∧
      (∀ j ∈ S, ∀ k ∈ S, j ≠ k → 10 * r < dist (q j) (q k)) ∧
      (∑ j, volume (Y j)) ≤ (⌈422400 / τ⌉₊ : ENNReal) * ∑ j ∈ S, volume (Y j) := by
  let A := Finset.univ.filter fun j => (Y j).Nonempty
  let R : Fin N → Fin N → Prop := fun j k =>
    j = k ∨ (j ∈ A ∧ k ∈ A ∧ dist (q j) (q k) ≤ 10 * r)
  have hD : 1 ≤ ⌈422400 / τ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hdeg (j : Fin N) : (Finset.univ.filter (R j)).card ≤ ⌈422400 / τ⌉₊ := by
    by_cases hj : j ∈ A
    · have hfilter : Finset.univ.filter (R j) =
          Finset.univ.filter (fun k => (Y k).Nonempty ∧ dist (q k) (q j) ≤ 10 * r) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          rcases h with rfl | ⟨_, hk, hd⟩
          · exact ⟨(Finset.mem_filter.mp hj).2, by simp; positivity⟩
          · exact ⟨(Finset.mem_filter.mp hk).2, by simpa only [dist_comm] using hd⟩
        · rintro ⟨hk, hd⟩
          exact Or.inr ⟨hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩,
            by simpa only [dist_comm] using hd⟩
      rw [hfilter]
      exact_mod_cast (nearby_tube_cells_count hδ hr hδr hτ x v hv Y q hY hYT hdisj hdense (q j)).trans
        (Nat.le_ceil _)
    · have heq : Finset.univ.filter (R j) = {j} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          R, hj, false_and, or_false, eq_comm]
      rw [heq, Finset.card_singleton]
      exact hD
  obtain ⟨S, hSA, hsep, hkeep⟩ := weighted_separated_subfamily R
    (fun _ => Or.inl rfl)
    (fun h => by
      rcases h with h | ⟨hj, hk, hd⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hk, hj, by simpa only [dist_comm] using hd⟩)
    ⌈422400 / τ⌉₊ hdeg (fun j => volume (Y j)) A
  refine ⟨S, fun j hj => (Finset.mem_filter.mp (hSA hj)).2, ?_, ?_⟩
  · intro j hj k hk hjk
    exact lt_of_not_ge (fun hd => hsep j hj k hk hjk (Or.inr ⟨hSA hj, hSA hk, hd⟩))
  · have hsum : (∑ j ∈ A, volume (Y j)) = ∑ j, volume (Y j) := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro j _ hj
      have hz : Y j = ∅ := not_nonempty_iff_eq_empty.mp (fun h =>
        hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      rw [hz, measure_empty]
    exact hsum ▸ hkeep

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
