import Submission.Obl.k4_scalar_marked_packet_recovery.Slicing

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open Set MeasureTheory
open scoped ENNReal

/-- The half-open time mesh has no overlapping cells. -/
theorem timeCell_disjoint {J : ℕ} (hJ : 0 < J) :
    Pairwise (fun z z' : Fin J => Disjoint (timeCell J z) (timeCell J z')) := by
  intro z z' hne
  have hJ' : 0 < (J : ℝ) := by exact_mod_cast hJ
  apply Set.disjoint_left.mpr
  intro t ht ht'
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
  · have hz : (z : ℝ) + 1 ≤ (z' : ℝ) := by exact_mod_cast h
    have hh := (div_le_div_iff_of_pos_right hJ').mpr hz
    exact (not_lt_of_ge (hh.trans ht'.1)) ht.2
  · have hz : (z' : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast h
    have hh := (div_le_div_iff_of_pos_right hJ').mpr hz
    exact (not_lt_of_ge (hh.trans ht.1)) ht'.2

theorem volume_timeCell {J : ℕ} (z : Fin J) :
    volume (timeCell J z) = ENNReal.ofReal (1 / (J : ℝ)) := by
  rw [Real.volume_Ico]
  congr 1
  ring

/-- Reference mass is the sum of its marked atom masses. -/
theorem referenceMass_eq_sum {H J : ℕ} (hJ : 0 < J)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (mark : Fin H → Fin J → Bool) (j : Fin H) :
    referenceMass w mark j = ∑ z : Fin J, if mark j z = true then
      ENNReal.ofReal (w j / (J : ℝ)) else 0 := by
  classical
  have heq : markTimes mark j = ⋃ z : Fin J,
      if mark j z = true then timeCell J z else ∅ := by
    ext t
    simp [markTimes]
  have hdisj : Pairwise (fun z z' : Fin J =>
      Disjoint (if mark j z = true then timeCell J z else ∅)
        (if mark j z' = true then timeCell J z' else ∅)) := by
    intro z z' hzz'
    split_ifs <;> simp_all [timeCell_disjoint hJ hzz']
  unfold referenceMass
  rw [heq, measure_iUnion hdisj (by intro z; split_ifs <;> measurability),
    tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hm : mark j z = true
  · simp only [hm, ite_true, volume_timeCell]
    simp only [div_eq_mul_inv, one_mul, ENNReal.ofReal_mul (hw j)]
  · simp [hm]

/-- Restore all original active mass of a marked tag, including the edge cells. -/
theorem restore_one_tag {α : Type*} [MeasurableSpace α] {H J : ℕ} (hJ : 0 < J)
    (μ : Measure (α × ℝ)) (tag : α → Fin H) (htag : Measurable tag)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (mark : Fin H → Fin J → Bool)
    {K : ℝ} (hK : 0 < K)
    (hfloor : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z}) (j : Fin H) :
    referenceMass w mark j ≤ ENNReal.ofReal K * μ ({l | tag l = j} ×ˢ Icc (0 : ℝ) 1) := by
  classical
  let C : Fin J → Set (α × ℝ) := fun z =>
    if mark j z = true then {p | tag p.1 = j ∧ p.2 ∈ timeCell J z} else ∅
  have hC : ∀ z, MeasurableSet (C z) := by
    intro z
    dsimp [C]
    split_ifs
    · exact (measurableSet_eq_fun (htag.comp measurable_fst) measurable_const).inter
        (measurableSet_Ico.preimage measurable_snd)
    · exact MeasurableSet.empty
  have hdisj : Pairwise (fun z z' => Disjoint (C z) (C z')) := by
    intro z z' hzz'
    dsimp [C]
    split_ifs <;> try simp
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact Set.disjoint_left.mp (timeCell_disjoint hJ hzz') hp.2 hp'.2
  rw [referenceMass_eq_sum hJ w hw mark j]
  calc
    _ ≤ ∑ z, ENNReal.ofReal K * μ (C z) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hm : mark j z = true
      · simp only [hm, ite_true, C]
        have heq : w j / (J : ℝ) = K * (w j / ((J : ℝ) * K)) := by
          field_simp
        rw [heq, ENNReal.ofReal_mul hK.le]
        gcongr
        exact hfloor j z hm
      · simp [hm, C]
    _ = ENNReal.ofReal K * μ (⋃ z, C z) := by
      rw [← Finset.mul_sum, measure_iUnion hdisj hC, tsum_fintype]
    _ ≤ _ := by
      gcongr
      intro p hp
      obtain ⟨z, hz⟩ := mem_iUnion.mp hp
      dsimp [C] at hz
      split_ifs at hz with hm
      · exact ⟨hz.1, timeCell_subset_unit hJ z hz.2⟩
      · exact hz.elim

/-- Sum restored masses over any collection of tags. -/
theorem restore_tag_set {α : Type*} [MeasurableSpace α] {H J : ℕ} (hJ : 0 < J)
    (μ : Measure (α × ℝ)) (tag : α → Fin H) (htag : Measurable tag)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (mark : Fin H → Fin J → Bool)
    {K : ℝ} (hK : 0 < K)
    (hfloor : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z}) (S : Finset (Fin H)) :
    (∑ j ∈ S, referenceMass w mark j) ≤
      ENNReal.ofReal K * μ ({l | tag l ∈ S} ×ˢ Icc (0 : ℝ) 1) := by
  classical
  calc
    _ ≤ ∑ j ∈ S, ENNReal.ofReal K * μ ({l | tag l = j} ×ˢ Icc (0 : ℝ) 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact restore_one_tag hJ μ tag htag w hw mark hK hfloor j
    _ = ENNReal.ofReal K * μ (⋃ j ∈ S, ({l | tag l = j} ×ˢ Icc (0 : ℝ) 1)) := by
      rw [← Finset.mul_sum, measure_biUnion_finset]
      · intro j hj j' hj' hne
        apply Set.disjoint_left.mpr
        intro p hp hp'
        exact hne (hp.1.symm.trans hp'.1)
      · intro j _
        exact (measurableSet_eq_fun htag measurable_const).prod measurableSet_Icc
    _ ≤ _ := by
      gcongr
      intro p hp
      obtain ⟨j, hp⟩ := mem_iUnion.mp hp
      obtain ⟨hj, hp⟩ := mem_iUnion.mp hp
      exact ⟨by change tag p.1 ∈ S; rw [hp.1]; exact hj, hp.2⟩

end Submission.Obl.k4_scalar_marked_packet_recovery
