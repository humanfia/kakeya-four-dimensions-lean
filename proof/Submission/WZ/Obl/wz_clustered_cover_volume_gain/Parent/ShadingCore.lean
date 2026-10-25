-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.ShadingCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.WeightedPruning
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ShadingAtoms

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory Set
open scoped Classical

noncomputable section

/-- Simultaneously enforce fiber density and a pointwise multiplicity threshold.
The loss is one sum of fiber thresholds plus the point threshold times the
original union volume. Zero-measure atoms are removed before reconstruction. -/
theorem measurable_shading_core {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (μ : Measure X) (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ⊤) (row : ι → κ) (cost : κ → ENNReal) (M : ENNReal) :
    ∃ Z : ι → Set X, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∑ i, μ (Y i)) ≤ (∑ i, μ (Z i)) + (∑ k, cost k) + M * μ (⋃ i, Y i) ∧
      (∀ k, (∃ i, row i = k ∧ (Z i).Nonempty) →
        cost k ≤ ∑ i ∈ Finset.univ.filter (fun i => row i = k), μ (Z i)) ∧
      (∀ p ∈ ⋃ i, Z i, M ≤ ((Finset.univ.filter fun i => p ∈ Z i).card : ENNReal)) := by
  classical
  let S : Finset (ι × Finset ι) := Finset.univ.filter fun a => a.1 ∈ a.2
  obtain ⟨T, hTS, hmass, hrow, hcol⟩ := weighted_bipartite_core S
    (fun a => row a.1) Prod.snd (fun a => μ (shadingAtom Y a.2)) cost
    (fun A => M * μ (shadingAtom Y A))
  let T' := T.filter fun a => μ (shadingAtom Y a.2) ≠ 0
  let Z := atomicShading Y T'
  have hZvol (i : ι) : μ (Z i) = μ (atomicShading Y T i) :=
    atomicShading_remove_null_mass μ hY T i
  have hsub (i : ι) : Z i ⊆ Y i := atomicShading_subset
    (fun a ha => (Finset.mem_filter.mp (hTS (Finset.mem_filter.mp ha).1)).2) i
  have hsumS : (∑ a ∈ S, μ (shadingAtom Y a.2)) = ∑ i, μ (Y i) := by
    rw [← atomicShading_mass μ hY]
    simp only [S, atomicShading_full]
  have hsumT : (∑ a ∈ T, μ (shadingAtom Y a.2)) = ∑ i, μ (Z i) := by
    simp_rw [hZvol]
    exact (atomicShading_mass μ hY T).symm
  refine ⟨Z, fun i => ⟨atomicShading_measurable hY T' i, hsub i⟩, ?_, ?_, ?_⟩
  · simpa only [hsumS, hsumT, ← Finset.mul_sum, sum_shadingAtom_volume μ hY] using hmass
  · intro k hk
    obtain ⟨i, hik, p, hp⟩ := hk
    have hiT : (i, shadingPattern Y p) ∈ T :=
      (Finset.mem_filter.mp (mem_atomicShading.mp hp).2).1
    have hh := hrow k ⟨(i, shadingPattern Y p), Finset.mem_filter.mpr ⟨hiT, hik⟩⟩
    simp_rw [hZvol]
    rw [atomicShading_row_mass μ hY]
    exact hh
  · intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    have hpY : p ∈ ⋃ i, Y i := Set.mem_iUnion.mpr ⟨i, hsub i hpi⟩
    let A := shadingPattern Y p
    letI : DecidablePred (fun a : ι × Finset ι => a.2 = A) :=
      fun _ => Classical.propDecidable _
    have hiT' : (i, A) ∈ T' := (mem_atomicShading.mp hpi).2
    have hA0 : μ (shadingAtom Y A) ≠ 0 := (Finset.mem_filter.mp hiT').2
    have hAtop : μ (shadingAtom Y A) ≠ ⊤ := shadingAtom_finite_volume μ hfin A
    have hc := hcol A ⟨(i, A), Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hiT').1, rfl⟩⟩
    have hsum : (∑ a ∈ T.filter (fun a => a.2 = A), μ (shadingAtom Y a.2)) =
        ((T.filter fun a => a.2 = A).card : ENNReal) * μ (shadingAtom Y A) := by
      calc
        _ = ∑ _a ∈ T.filter (fun a => a.2 = A), μ (shadingAtom Y A) :=
          Finset.sum_congr rfl fun a ha => congrArg (fun B => μ (shadingAtom Y B))
            (Finset.mem_filter.mp ha).2
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at hc
    have hcard : (T.filter fun a => a.2 = A).card =
        (Finset.univ.filter fun i => p ∈ Z i).card := by
      apply Finset.card_bij (fun a _ => a.1)
      · intro a ha
        obtain ⟨haT, haA⟩ := Finset.mem_filter.mp ha
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, mem_atomicShading.mpr ⟨hpY, ?_⟩⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, hA0⟩
        simpa only [A, ← haA, Prod.eta] using haT
      · intro a ha b hb hab
        exact Prod.ext hab ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      · intro j hj
        have hjT' : (j, A) ∈ T' := (mem_atomicShading.mp (Finset.mem_filter.mp hj).2).2
        exact ⟨(j, A), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hjT').1, rfl⟩, rfl⟩
    rw [hcard] at hc
    exact (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp hc

theorem measurable_shading_core_half {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (μ : Measure X) (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ⊤) (row : ι → κ) (cost : κ → ENNReal) (M : ENNReal)
    (hbudget : (∑ k, cost k) + M * μ (⋃ i, Y i) ≤ (1 / 2 : ENNReal) * ∑ i, μ (Y i)) :
    ∃ Z : ι → Set X, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (1 / 2 : ENNReal) * (∑ i, μ (Y i)) ≤ ∑ i, μ (Z i) ∧
      (∀ k, (∃ i, row i = k ∧ (Z i).Nonempty) →
        cost k ≤ ∑ i ∈ Finset.univ.filter (fun i => row i = k), μ (Z i)) ∧
      (∀ p ∈ ⋃ i, Z i, M ≤ ((Finset.univ.filter fun i => p ∈ Z i).card : ENNReal)) := by
  obtain ⟨Z, hZ, hmass, hrow, hpoint⟩ := measurable_shading_core μ Y hY hfin row cost M
  refine ⟨Z, hZ, ?_, hrow, hpoint⟩
  have hh : (∑ i, μ (Y i)) ≤ (∑ i, μ (Z i)) + (1 / 2 : ENNReal) * ∑ i, μ (Y i) := by
    exact hmass.trans ((add_assoc _ _ _).le.trans (add_le_add le_rfl hbudget))
  have he : (1 / 2 : ENNReal) * (∑ i, μ (Y i)) + (1 / 2 : ENNReal) * (∑ i, μ (Y i)) =
      ∑ i, μ (Y i) := by rw [← add_mul]; norm_num [ENNReal.inv_two_add_inv_two]
  nth_rw 1 [← he] at hh
  exact ENNReal.le_of_add_le_add_right
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun i _ => hfin i)) hh

end

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
