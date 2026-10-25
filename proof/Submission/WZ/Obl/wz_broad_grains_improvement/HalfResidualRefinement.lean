-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.HalfResidualRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.ResidualFibreLevel
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.FibreRetention
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenBridge
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.CrossScaleCount

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open scoped ENNReal Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (fiberBodyCount supported_fine_count)

/-- A half-mass residual admits one common fibre level while keeping a fixed
fraction of the old incidences at every retained fibre point. -/
theorem half_residual_uniform_refinement {n N : ℕ} (S : Finset (Fin n))
    (f : Fin n → Fin N) {Z R : Fin n → Set V}
    (hZm : ∀ i, MeasurableSet (Z i)) (hRm : ∀ i, MeasurableSet (R i))
    (hZfin : ∀ i, volume (Z i) ≠ ⊤) (hRZ : ∀ i, R i ⊆ Z i)
    (hZoff : ∀ i, i ∉ S → Z i = ∅)
    (hretain : (1/2:ENNReal) * ∑ i,volume (Z i) ≤ ∑ i,volume (R i)) :
    ∃ (W : Fin n → Set V) (m : ℝ), 0 < m ∧
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ R i ∧ (i ∉ S → W i = ∅)) ∧
      O (1/4) * ∑ i,volume (Z i) ≤ (Nat.log 2 n+1:ℕ) * ∑ i,volume (W i) ∧
      (∀ k p, (∃ i ∈ S, f i=k ∧ p ∈ W i) →
        q n {i | i ∈ S ∧ f i=k ∧ p ∈ Z i} ≤
          4*q n {i | i ∈ S ∧ f i=k ∧ p ∈ W i}) ∧
      ∀ k p, (∃ i ∈ S, f i=k ∧ p ∈ W i) →
        q n {i | i ∈ S ∧ f i=k ∧ p ∈ W i} ∈ Icc m (2*m) := by
  obtain ⟨U,hU,hUmass,hUfrac⟩ :=
    WangZahlLot.Obl.wz_move_two_dense_broad_prisms.retain_fibre_incidence_fraction
      f hZm hRm hZfin hRZ hretain
  have hUoff : ∀ i, i ∉ S → U i = ∅ := fun i hi =>
    subset_empty_iff.mp (((hU i).2.trans (hRZ i)).trans (by rw [hZoff i hi]))
  have hUsum : (∑ i ∈ S,volume (U i)) = ∑ i,volume (U i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [hUoff i hi]
  obtain ⟨k,W,hW,hWmass,hWlevel⟩ := fibre_dyadic_level_common volume S f U (fun i => (hU i).1)
  have hWoff : ∀ i, i ∉ S → W i = ∅ := fun i => (hW i).2.2
  have hcount (j : Fin N) (p : V) : q n {i | i ∈ S ∧ f i=j ∧ p ∈ W i} =
      ((Finset.univ.filter fun i => f i=j ∧ p ∈ W i).card:ℝ) := by
    have he : {i | i ∈ S ∧ f i=j ∧ p ∈ W i} = {i | f i=j ∧ p ∈ W i} := by
      ext i
      constructor
      · exact fun hi => hi.2
      · intro hi
        refine ⟨?_,hi⟩
        by_contra hh
        simpa only [hWoff i hh,mem_empty_iff_false] using hi.2
    simp [q,he,Set.ncard_eq_toFinset_card']
  refine ⟨W,(2:ℝ)^k,by positivity,fun i =>
    ⟨(hW i).1,(hW i).2.1.trans (hU i).2,(hW i).2.2⟩,
    hUmass.trans (by simpa only [hUsum] using hWmass),?_,?_⟩
  · intro j p hp
    obtain ⟨i,hi,hfi,hpi⟩ := hp
    have hlev := hWlevel j p ⟨i,hfi,hpi⟩
    have he : {i | i ∈ S ∧ f i=j ∧ p ∈ W i} =
        {i | i ∈ S ∧ f i=j ∧ p ∈ U i} := by
      ext l
      constructor
      · exact fun hl => ⟨hl.1,hl.2.1,(hW l).2.1 hl.2.2⟩
      · exact fun hl => ⟨hl.1,hl.2.1,(hlev.2.2 l hl.2.1).mpr ⟨hl.1,hl.2.2⟩⟩
    rw [he]
    have hh := hUfrac j p ⟨i,hfi,(hW i).2.1 hpi⟩
    simpa only [← supported_fine_count f hZoff,← supported_fine_count f hUoff] using hh
  · intro j p hp
    obtain ⟨i,hi,hfi,hpi⟩ := hp
    have hlev := hWlevel j p ⟨i,hfi,hpi⟩
    rw [hcount]
    constructor
    · exact_mod_cast hlev.1
    · have hh := hlev.2.1.le
      rw [pow_succ,mul_comm] at hh
      exact_mod_cast hh

end WangZahlLot.Obl.wz_broad_grains_improvement
