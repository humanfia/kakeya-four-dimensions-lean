import Submission.Obl.k4_scalar_marked_coefficient_smoothing.TimeCells

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory Set
open scoped ENNReal

theorem noise_probability {σ : ℝ} (hσ : 0 < σ) : IsProbabilityMeasure (Noise σ) := by
  have hcoord : IsProbabilityMeasure
      (ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc (0 : ℝ) σ)) := by
    apply isProbabilityMeasure_iff.mpr
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hσ.ne', ENNReal.ofReal_one]
  haveI : ∀ i : Fin 5, IsProbabilityMeasure
      (ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc (0 : ℝ) σ)) := fun _ => hcoord
  unfold Noise
  infer_instance

theorem markedPrior_tag_mass {σ : ℝ} (hσ : 0 < σ) (H : ℕ)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (j : Fin H) :
    MarkedPrior σ H b₀ w {l | l.1 = (j : ℕ)} = ENNReal.ofReal (w j) := by
  classical
  haveI := noise_probability hσ
  rw [MarkedPrior, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [Measure.map_apply (by fun_prop) (by measurability)]
    simp
  · intro i _ hij
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [hne]
  · simp

theorem markedPrior_probability {σ : ℝ} (hσ : 0 < σ) (H : ℕ)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : (∑ j, w j) = 1) :
    IsProbabilityMeasure (MarkedPrior σ H b₀ w) := by
  classical
  haveI := noise_probability hσ
  apply isProbabilityMeasure_iff.mpr
  rw [MarkedPrior, Measure.finsetSum_apply]
  have heq : (∑ j : Fin H, (ENNReal.ofReal (w j) •
      Measure.map (fun u : Coeff => ((j : ℕ), b₀ j + u)) (Noise σ)) univ) =
        ∑ j : Fin H, ENNReal.ofReal (w j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  rw [heq, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw j), hsum, ENNReal.ofReal_one]

theorem markedEvent_eq_iUnion (H J : ℕ) (mark : Fin H → Fin J → Bool) :
    MarkedEvent H J mark = ⋃ q : Fin H × Fin J,
      if mark q.1 q.2 = true then
        {l : Traj | l.1 = (q.1 : ℕ)} ×ˢ timeCell J q.2 else ∅ := by
  classical
  ext p
  simp only [MarkedEvent, mem_setOf_eq, mem_iUnion, Prod.exists]
  constructor
  · rintro ⟨j, hj, z, hz, ht⟩
    exact ⟨j, z, by simpa [hz] using And.intro hj ht⟩
  · rintro ⟨j, z, hp⟩
    by_cases hz : mark j z = true
    · have hp' : p.1.1 = (j : ℕ) ∧ p.2 ∈ timeCell J z := by simpa [hz] using hp
      exact ⟨j, hp'.1, z, hz, hp'.2⟩
    · simp [hz] at hp

theorem measurableSet_markedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) :
    MeasurableSet (MarkedEvent H J mark) := by
  classical
  rw [markedEvent_eq_iUnion]
  apply MeasurableSet.iUnion
  intro q
  split_ifs
  · exact (by measurability : MeasurableSet {l : Traj | l.1 = (q.1 : ℕ)}).prod
      (measurableSet_timeCell J q.2)
  · exact MeasurableSet.empty

theorem markedLaw_total_mass {σ : ℝ} (hσ : 0 < σ) {H J : ℕ} (hJ : 0 < J)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (mark : Fin H → Fin J → Bool) :
    MarkedLaw σ H J b₀ w mark univ =
      ENNReal.ofReal (∑ j, ∑ z, if mark j z = true then w j / (J : ℝ) else 0) := by
  classical
  rw [MarkedLaw, Measure.restrict_apply_univ, markedEvent_eq_iUnion]
  have hdisj : Pairwise (fun q q' : Fin H × Fin J => Disjoint
      (if mark q.1 q.2 = true then {l : Traj | l.1 = (q.1 : ℕ)} ×ˢ timeCell J q.2 else ∅)
      (if mark q'.1 q'.2 = true then {l : Traj | l.1 = (q'.1 : ℕ)} ×ˢ timeCell J q'.2 else ∅)) := by
    intro q q' hne
    split_ifs with h h'
    · rw [Set.disjoint_left]
      intro p hp hp'
      have hj : q.1 = q'.1 := Fin.ext (hp.1.symm.trans hp'.1)
      have hz : q.2 ≠ q'.2 := fun hz => hne (Prod.ext hj hz)
      exact Set.disjoint_left.mp (timeCell_disjoint hJ hz) hp.2 hp'.2
    all_goals simp
  have hmeas (q : Fin H × Fin J) : MeasurableSet
      (if mark q.1 q.2 = true then {l : Traj | l.1 = (q.1 : ℕ)} ×ˢ timeCell J q.2 else ∅) := by
    split_ifs
    · exact (by measurability : MeasurableSet {l : Traj | l.1 = (q.1 : ℕ)}).prod
        (measurableSet_timeCell J q.2)
    · exact MeasurableSet.empty
  rw [measure_iUnion hdisj hmeas, tsum_fintype, Fintype.sum_prod_type]
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hnonneg (j : Fin H) (z : Fin J) :
      0 ≤ (if mark j z = true then w j / (J : ℝ) else 0) := by
    split_ifs
    · exact div_nonneg (hw j) hJr.le
    · exact le_rfl
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    Finset.sum_nonneg (fun z _ => hnonneg j z))]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_sum_of_nonneg (fun z _ => hnonneg j z)]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with h
  · rw [Measure.prod_prod, markedPrior_tag_mass hσ, volume_timeCell hJ,
      ← ENNReal.ofReal_mul (hw j)]
    congr 1
    ring
  · simp

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
