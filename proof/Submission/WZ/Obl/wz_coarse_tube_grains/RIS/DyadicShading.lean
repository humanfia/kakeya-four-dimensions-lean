-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.DyadicShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.ShadingAtoms
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory Set
open scoped Classical

noncomputable section

/-- A common dyadic multiplicity level retains one logarithmic share of the
original shading mass. The multiplicity bounds hold at every retained point. -/
theorem dyadic_shading_refinement_common {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i)) :
    ∃ (k : ℕ) (Z : ι → Set X), k ≤ Nat.log 2 (Fintype.card ι) ∧
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∑ i, μ (Y i)) ≤ (Nat.log 2 (Fintype.card ι) + 1 : ℕ) * ∑ i, μ (Z i) ∧
      ∀ p ∈ ⋃ i, Z i,
        2 ^ k ≤ (Finset.univ.filter fun i => p ∈ Z i).card ∧
        (Finset.univ.filter fun i => p ∈ Z i).card < 2 ^ (k + 1) ∧
        (∀ i, p ∈ Z i ↔ p ∈ Y i) := by
  classical
  let K := Nat.log 2 (Fintype.card ι) + 1
  let S : Finset (ι × Finset ι) := Finset.univ.filter fun a => a.1 ∈ a.2
  let col : ι × Finset ι → Fin K := fun a =>
    ⟨Nat.log 2 a.2.card, Nat.lt_succ_of_le (Nat.log_mono_right a.2.card_le_univ)⟩
  obtain ⟨k, hmass⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    (show 0 < K by dsimp [K]; omega) S col (fun a => μ (shadingAtom Y a.2))
  let T := S.filter fun a => col a = k
  let Z := atomicShading Y T
  have hsub (i : ι) : Z i ⊆ Y i := atomicShading_subset
    (fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2) i
  have hsumS : (∑ a ∈ S, μ (shadingAtom Y a.2)) = ∑ i, μ (Y i) := by
    rw [← atomicShading_mass μ hY]
    simp only [S, atomicShading_full]
  have hsumT : (∑ a ∈ T, μ (shadingAtom Y a.2)) = ∑ i, μ (Z i) :=
    (atomicShading_mass μ hY T).symm
  refine ⟨k.1, Z, by have hk := k.isLt; dsimp [K] at hk; omega,
    fun i => ⟨atomicShading_measurable hY T i, hsub i⟩, ?_, ?_⟩
  · change (∑ i, μ (Y i)) ≤ (K : ENNReal) * ∑ i, μ (Z i)
    change (∑ a ∈ S, μ (shadingAtom Y a.2)) ≤ (K : ENNReal) *
      ∑ a ∈ T, μ (shadingAtom Y a.2) at hmass
    simpa only [hsumS, hsumT] using hmass
  · intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    have hpY : p ∈ ⋃ i, Y i := Set.mem_iUnion.mpr ⟨i, hsub i hpi⟩
    let A := shadingPattern Y p
    have hiT : (i, A) ∈ T := (mem_atomicShading.mp hpi).2
    have hcol : col (i, A) = k := (Finset.mem_filter.mp hiT).2
    have hlog : Nat.log 2 A.card = k.1 := congrArg Fin.val hcol
    have hiA : i ∈ A := (Finset.mem_filter.mp (Finset.mem_filter.mp hiT).1).2
    have hA : A.card ≠ 0 := Finset.card_ne_zero.mpr ⟨i, hiA⟩
    have hcols (j : ι) : col (j, A) = k := Fin.ext hlog
    have hmem (j : ι) : p ∈ Z j ↔ j ∈ A := by
      rw [mem_atomicShading]
      simp only [hpY, true_and]
      change (j, A) ∈ T ↔ _
      simp only [T, S, Finset.mem_filter, Finset.mem_univ, true_and, hcols j, and_true]
    have hcard : (Finset.univ.filter fun j => p ∈ Z j).card = A.card := by
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmem]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcard, ← hlog]
      exact Nat.pow_log_le_self 2 hA
    · rw [hcard, ← hlog]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    · intro j
      simpa only [A, shadingPattern, Finset.mem_filter, Finset.mem_univ, true_and] using hmem j

/-- The multiplicity-level refinement, omitting the common-cut property. -/
theorem dyadic_shading_refinement {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i)) :
    ∃ (k : ℕ) (Z : ι → Set X), k ≤ Nat.log 2 (Fintype.card ι) ∧
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∑ i, μ (Y i)) ≤ (Nat.log 2 (Fintype.card ι) + 1 : ℕ) * ∑ i, μ (Z i) ∧
      ∀ p ∈ ⋃ i, Z i,
        2 ^ k ≤ (Finset.univ.filter fun i => p ∈ Z i).card ∧
        (Finset.univ.filter fun i => p ∈ Z i).card < 2 ^ (k + 1) := by
  obtain ⟨k, Z, hk, hZ, hmass, hlevel⟩ := dyadic_shading_refinement_common μ Y hY
  exact ⟨k, Z, hk, hZ, hmass, fun p hp => ⟨(hlevel p hp).1, (hlevel p hp).2.1⟩⟩

end

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
