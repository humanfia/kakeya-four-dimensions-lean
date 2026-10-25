-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.UnionMultiplicityCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.ShadingAtoms
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyRefinement
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (bodyCount)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
  (shadingAtom shadingPattern mem_shadingPattern shadingAtom_measurable
   shadingAtom_disjoint sum_shadingAtom_volume shadingAtom_eq_pattern)

/-- A common multiplicity level can be selected by physical union volume.
This conclusion does not assert retention of the original incidence mass. -/
theorem common_multiplicity_union_cut {n : ℕ} (W : Fin n → Set V)
    (hW : ∀ i, MeasurableSet (W i)) :
    ∃ (C : Set V) (m : ℝ), MeasurableSet C ∧ C ⊆ ⋃ i,W i ∧ 0 < m ∧
      volume (⋃ i,W i) ≤ (Nat.log 2 n+1:ℕ)*volume C ∧
      ∀ p ∈ C, bodyCount W p ∈ Icc m (2*m) := by
  classical
  let K := Nat.log 2 n+1
  let col (A : Finset (Fin n)) : Fin K := ⟨Nat.log 2 A.card, by
    have hh := Nat.log_mono_right A.card_le_univ (b := 2)
    simpa only [Fintype.card_fin,K] using Nat.lt_succ_of_le hh⟩
  obtain ⟨k,hk⟩ := WangZahlLot.Obl.wz_tower_balanced_refinement.weighted_color
    (show 0<K by dsimp [K]; omega) Finset.univ col (fun A => volume (shadingAtom W A))
  let S := Finset.univ.filter fun A => col A=k
  let C := ⋃ A ∈ S, shadingAtom W A
  have hCm : MeasurableSet C := Finset.measurableSet_biUnion S
    (fun A _ => shadingAtom_measurable hW A)
  have hsub : C ⊆ ⋃ i,W i := iUnion₂_subset fun _ _ => inter_subset_left
  have hvol : volume C = ∑ A ∈ S,volume (shadingAtom W A) :=
    measure_biUnion_finset (fun _ _ _ _ hne => shadingAtom_disjoint W hne)
      (fun A _ => shadingAtom_measurable hW A)
  refine ⟨C,(2:ℝ)^(k:ℕ),hCm,hsub,by positivity,?_,?_⟩
  · rw [hvol]
    simpa only [sum_shadingAtom_volume volume hW] using hk
  · intro p hp
    obtain ⟨A,hA,hpA⟩ := mem_iUnion₂.mp hp
    have hlog : Nat.log 2 A.card=(k:ℕ) := congrArg Fin.val (Finset.mem_filter.mp hA).2
    have hne : A.card ≠ 0 := by
      obtain ⟨i,hi⟩ := mem_iUnion.mp hpA.1
      exact Finset.card_ne_zero.mpr ⟨i,(hpA.2 i).mp hi⟩
    have hcount : bodyCount W p=(A.card:ℝ) := by
      rw [shadingAtom_eq_pattern hpA]
      simp [bodyCount,shadingPattern,Set.ncard_eq_toFinset_card']
    rw [hcount]
    have hlo := Nat.pow_log_le_self 2 hne
    have hhi := (Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) A.card).le
    rw [hlog] at hlo hhi
    constructor
    · exact_mod_cast hlo
    · rw [pow_succ,mul_comm] at hhi
      exact_mod_cast hhi

end WangZahlLot.Obl.wz_broad_grains_improvement
