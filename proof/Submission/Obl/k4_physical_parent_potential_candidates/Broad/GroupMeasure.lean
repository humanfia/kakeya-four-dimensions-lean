-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/GroupMeasure.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.DiagonalFrame
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.LightCells

/-!
# Measures of unions of whole observation cells

Group events are unions of whole observation cells (base cube of side `p` times hidden bin of
`obs Bv a`), cut to the source set `Hs`. This file transfers per-cell information to them.

* `measure_cells_base_le`: if every base region carries, in each single hidden bin, mass at most
  `cap` times its volume, and the cell set uses at most `Kb` bins above each cube, then the
  union carries mass at most `Kb cap` times the volume of its base region.
* `measure_cells_inter_le`: a fractional bound `μ(cell ∩ Z) ≤ κ μ(cell)` holding for every cell
  holds for every union of whole cells (countable additivity).
* `volume_frame_preimage`: in the diagonal frame, base regions of normalized volume `V` have
  physical volume `2h D² V`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The cube cells cover the base space. -/
lemma iUnion_cubeSet (p : ℝ) : (⋃ c : Fin 3 → ℤ, cubeSet p c) = univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun e => ⌊z e / p⌋, fun e => rfl⟩

/-- **Base density of a union of cells.** -/
theorem measure_cells_base_le (μ : Measure Ev) (Hs : Set Ev) (S : Set ((Fin 3 → ℤ) × ℤ))
    {p Bv a cap : ℝ} (Kb : ℕ)
    (hbins : ∀ c : Fin 3 → ℤ, ∃ Fc : Finset ℤ, Fc.card ≤ Kb ∧ ∀ k, (c, k) ∈ S → k ∈ Fc)
    (hcap : ∀ U : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet U → ∀ n : ℤ,
      μ (Hs ∩ {q | basePoint q ∈ U ∧ binIdx Bv a q = n}) ≤ ENNReal.ofReal cap * volume U)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    μ (cellIdx p Bv a ⁻¹' S ∩ Hs ∩ {q | basePoint q ∈ U}) ≤
      ENNReal.ofReal cap * Kb * volume U := by
  classical
  choose Fc hFc hFcS using hbins
  have hsub : cellIdx p Bv a ⁻¹' S ∩ Hs ∩ {q | basePoint q ∈ U} ⊆
      ⋃ c : Fin 3 → ℤ, ⋃ k ∈ Fc c,
        (Hs ∩ {q | basePoint q ∈ U ∩ cubeSet p c ∧ binIdx Bv a q = k}) := by
    intro q hq
    obtain ⟨⟨hqS, hqH⟩, hqU⟩ := hq
    refine Set.mem_iUnion.mpr ⟨cubeIdx p q, Set.mem_iUnion₂.mpr ⟨binIdx Bv a q,
      hFcS _ _ hqS, hqH, ⟨hqU, ?_⟩, rfl⟩⟩
    exact (basePoint_mem_cubeSet_iff p _ q).mpr rfl
  have hcube : ∀ c, MeasurableSet (U ∩ cubeSet p c) := fun c => hU.inter (measurableSet_cubeSet p c)
  calc μ (cellIdx p Bv a ⁻¹' S ∩ Hs ∩ {q | basePoint q ∈ U})
      ≤ μ (⋃ c : Fin 3 → ℤ, ⋃ k ∈ Fc c,
          (Hs ∩ {q | basePoint q ∈ U ∩ cubeSet p c ∧ binIdx Bv a q = k})) := measure_mono hsub
    _ ≤ ∑' c : Fin 3 → ℤ, μ (⋃ k ∈ Fc c,
          (Hs ∩ {q | basePoint q ∈ U ∩ cubeSet p c ∧ binIdx Bv a q = k})) :=
        measure_iUnion_le _
    _ ≤ ∑' c : Fin 3 → ℤ, ∑ k ∈ Fc c,
          μ (Hs ∩ {q | basePoint q ∈ U ∩ cubeSet p c ∧ binIdx Bv a q = k}) :=
        ENNReal.tsum_le_tsum fun c => measure_biUnion_finset_le _ _
    _ ≤ ∑' c : Fin 3 → ℤ, ∑ _k ∈ Fc c, ENNReal.ofReal cap * volume (U ∩ cubeSet p c) :=
        ENNReal.tsum_le_tsum fun c => Finset.sum_le_sum fun k _ => hcap _ (hcube c) k
    _ ≤ ∑' c : Fin 3 → ℤ, (Kb : ℝ≥0∞) * (ENNReal.ofReal cap * volume (U ∩ cubeSet p c)) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast hFc c
    _ = (Kb : ℝ≥0∞) * ENNReal.ofReal cap * ∑' c : Fin 3 → ℤ, volume (U ∩ cubeSet p c) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, mul_assoc]
    _ = (Kb : ℝ≥0∞) * ENNReal.ofReal cap * volume U := by
        congr 1
        rw [← measure_iUnion]
        · congr 1
          rw [← Set.inter_iUnion, iUnion_cubeSet, Set.inter_univ]
        · intro c c' hcc'
          exact (disjoint_cubeSet hcc').mono Set.inter_subset_right Set.inter_subset_right
        · exact hcube
    _ = ENNReal.ofReal cap * Kb * volume U := by ring

/-- **Fractional bounds pass to unions of whole cells.** -/
theorem measure_cells_inter_le (μ : Measure Ev) (Hs : Set Ev) (hHs : MeasurableSet Hs)
    {p Bv a : ℝ} (Z : Set Ev) (hZ : MeasurableSet Z) (κ : ℝ≥0∞)
    (hcell : ∀ k, μ (Hs ∩ cellIdx p Bv a ⁻¹' {k} ∩ Z) ≤ κ * μ (Hs ∩ cellIdx p Bv a ⁻¹' {k}))
    (S : Set ((Fin 3 → ℤ) × ℤ)) :
    μ (Hs ∩ cellIdx p Bv a ⁻¹' S ∩ Z) ≤ κ * μ (Hs ∩ cellIdx p Bv a ⁻¹' S) := by
  have hcountable : S.Countable := Set.to_countable S
  have hmeas : ∀ k, MeasurableSet (cellIdx p Bv a ⁻¹' {k}) :=
    fun k => measurable_cellIdx p Bv a (measurableSet_singleton k)
  have hU : ∀ T : Set Ev, Hs ∩ cellIdx p Bv a ⁻¹' S ∩ T =
      ⋃ k ∈ S, (Hs ∩ cellIdx p Bv a ⁻¹' {k} ∩ T) := by
    intro T
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨⟨hH, hS⟩, hT⟩; exact ⟨_, hS, ⟨hH, rfl⟩, hT⟩
    · rintro ⟨k, hk, ⟨hH, rfl⟩, hT⟩; exact ⟨⟨hH, hk⟩, hT⟩
  have hdisj : ∀ T : Set Ev, S.PairwiseDisjoint (fun k => Hs ∩ cellIdx p Bv a ⁻¹' {k} ∩ T) := by
    intro T k _ k' _ hkk'
    refine Set.disjoint_left.mpr fun q hq hq' => hkk' ?_
    exact hq.1.2.symm.trans hq'.1.2
  have hS2 : Hs ∩ cellIdx p Bv a ⁻¹' S = Hs ∩ cellIdx p Bv a ⁻¹' S ∩ univ := by
    rw [Set.inter_univ]
  calc μ (Hs ∩ cellIdx p Bv a ⁻¹' S ∩ Z)
      = ∑' k : S, μ (Hs ∩ cellIdx p Bv a ⁻¹' {(k : (Fin 3 → ℤ) × ℤ)} ∩ Z) := by
        rw [hU Z, measure_biUnion hcountable (hdisj Z)
          (fun k _ => (hHs.inter (hmeas k)).inter hZ)]
    _ ≤ ∑' k : S, κ * μ (Hs ∩ cellIdx p Bv a ⁻¹' {(k : (Fin 3 → ℤ) × ℤ)}) :=
        ENNReal.tsum_le_tsum fun k => hcell k
    _ = κ * ∑' k : S, μ (Hs ∩ cellIdx p Bv a ⁻¹' {(k : (Fin 3 → ℤ) × ℤ)}) :=
        ENNReal.tsum_mul_left
    _ = κ * μ (Hs ∩ cellIdx p Bv a ⁻¹' S) := by
        congr 1
        have h := hU univ
        rw [← hS2] at h
        rw [h, measure_biUnion hcountable (hdisj univ)
          (fun k _ => (hHs.inter (hmeas k)).inter MeasurableSet.univ)]
        simp only [Set.inter_univ]

/-- **Volumes in the diagonal frame.**  The physical base region whose normalized image lies in
`U` has volume `2h D²` times that of `U`. -/
theorem volume_frame_preimage {h D : ℝ} (hh : 0 < h) (hD : 0 < D) (z₀ : Fin 3 → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    volume {z : EuclideanSpace ℝ (Fin 3) |
        (WithLp.toLp 2 (fun i => (z i - z₀ i) / frameScale h D i) : EuclideanSpace ℝ (Fin 3)) ∈ U} =
      ENNReal.ofReal (2 * h * D ^ 2) * volume U := by
  set s := frameScale h D with hs
  have hs0 : ∀ i, 0 < s i := frameScale_pos hh hD
  set L : (Fin 3 → ℝ) →ₗ[ℝ] Fin 3 → ℝ := Matrix.toLin' (Matrix.diagonal fun i => (s i)⁻¹) with hL
  have hdet : LinearMap.det L = ∏ i, (s i)⁻¹ := by
    rw [hL, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]; exact Finset.prod_ne_zero_iff.mpr fun i _ => (inv_pos.mpr (hs0 i)).ne'
  have hprod : (∏ i, s i) = 2 * h * D ^ 2 := by
    rw [Fin.prod_univ_three, hs]; simp [frameScale]; ring
  -- move to coordinates
  have hpres := PiLp.volume_preserving_toLp (Fin 3)
  have hset : (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
      {z : EuclideanSpace ℝ (Fin 3) |
        (WithLp.toLp 2 (fun i => (z i - z₀ i) / s i) : EuclideanSpace ℝ (Fin 3)) ∈ U} =
      (fun x : Fin 3 → ℝ => x - z₀) ⁻¹' (L ⁻¹' ((WithLp.toLp 2) ⁻¹' U)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hL]
    have : (fun i => (x i - z₀ i) / s i) = Matrix.toLin' (Matrix.diagonal fun i => (s i)⁻¹) (x - z₀) := by
      funext i
      rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
      simp [div_eq_mul_inv, mul_comm]
    rw [this]
  have hU' : volume ((WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹' U) =
      volume U := hpres.measure_preimage hU.nullMeasurableSet
  have hVm : MeasurableSet {z : EuclideanSpace ℝ (Fin 3) |
      (WithLp.toLp 2 (fun i => (z i - z₀ i) / s i) : EuclideanSpace ℝ (Fin 3)) ∈ U} := by
    refine (Measurable.comp (PiLp.continuous_toLp 2 _).measurable ?_) hU
    refine measurable_pi_iff.mpr fun i => ?_
    exact ((measurable_pi_apply i).comp (PiLp.volume_preserving_ofLp (Fin 3)).measurable).sub_const _
      |>.div_const _
  rw [← hpres.measure_preimage hVm.nullMeasurableSet, hset]
  have htrans : volume ((fun x : Fin 3 → ℝ => x - z₀) ⁻¹' (L ⁻¹' ((WithLp.toLp 2) ⁻¹' U))) =
      volume (L ⁻¹' ((WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) ⁻¹' U)) := by
    have : (fun x : Fin 3 → ℝ => x - z₀) = fun x => x + (-z₀) := by funext x; ring
    rw [this, measure_preimage_add_right]
  rw [htrans, Measure.addHaar_preimage_linearMap volume hdet0, hU', hdet, ← hprod]
  congr 2
  rw [Finset.prod_inv_distrib, inv_inv, abs_of_pos (Finset.prod_pos fun i _ => hs0 i)]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
