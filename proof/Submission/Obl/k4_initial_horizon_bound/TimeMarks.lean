import Submission.Obl.k4_initial_horizon_bound.Duration
import Submission.Obl.k4_scalar_coefficient_clustering.TimeBins

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_initial_horizon_bound

open Submission.Obl.k4_scalar_coefficient_clustering (timeCell exists_timeCell)

noncomputable def positiveTimeMarks {α : Type*} (D : ℕ) (E : Set (α × ℝ))
    (x : α) : Finset (Fin D) := by
  classical
  exact Finset.univ.filter (fun j => 0 < volume ((Prod.mk x ⁻¹' E) ∩ timeCell D j))

theorem measurable_positiveTimeMarks {α : Type*} [MeasurableSpace α]
    (D : ℕ) {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    Measurable (positiveTimeMarks D E) := by
  classical
  apply measurable_finset_iff.mpr
  intro j
  have hm : Measurable (fun x => volume ((Prod.mk x ⁻¹' E) ∩ timeCell D j)) := by
    have hm := measurable_incidenceDuration (hE.inter (MeasurableSet.univ.prod measurableSet_Icc))
      (E := E ∩ (univ ×ˢ timeCell D j))
    change Measurable (fun x => volume (Prod.mk x ⁻¹' (E ∩ (univ ×ˢ timeCell D j)))) at hm
    have heq (x : α) : Prod.mk x ⁻¹' (E ∩ (univ ×ˢ timeCell D j)) =
        (Prod.mk x ⁻¹' E) ∩ timeCell D j := by
      ext t
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]
    simpa only [heq] using hm
  simp only [positiveTimeMarks, Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const hm)

theorem positiveTimeMarks_witness {α : Type*} {D : ℕ} {E : Set (α × ℝ)}
    {x : α} {j : Fin D} (hj : j ∈ positiveTimeMarks D E x) :
    ∃ t, (x, t) ∈ E ∧ t ∈ timeCell D j := by
  classical
  have hpos : 0 < volume ((Prod.mk x ⁻¹' E) ∩ timeCell D j) :=
    (Finset.mem_filter.mp hj).2
  exact nonempty_of_measure_ne_zero hpos.ne'

theorem positiveTimeMarks_witness_interior {α : Type*} {D : ℕ} {E : Set (α × ℝ)}
    {x : α} {j : Fin D} (hj : j ∈ positiveTimeMarks D E x) :
    ∃ t, (x, t) ∈ E ∧ t ∈ Ioo (((j : ℕ) : ℝ) / D) ((((j : ℕ) : ℝ) + 1) / D) := by
  classical
  have hpos : 0 < volume ((Prod.mk x ⁻¹' E) ∩ timeCell D j) :=
    (Finset.mem_filter.mp hj).2
  have hae : (Prod.mk x ⁻¹' E) ∩ Ioo (((j : ℕ) : ℝ) / D)
      ((((j : ℕ) : ℝ) + 1) / D) =ᵐ[volume] (Prod.mk x ⁻¹' E) ∩ timeCell D j := by
    filter_upwards [Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))
      (a := (((j : ℕ) : ℝ) / D)) (b := ((((j : ℕ) : ℝ) + 1) / D))] with t ht
    exact congrArg (fun q : Prop => t ∈ Prod.mk x ⁻¹' E ∧ q) ht
  have hpos' : 0 < volume ((Prod.mk x ⁻¹' E) ∩ Ioo (((j : ℕ) : ℝ) / D)
      ((((j : ℕ) : ℝ) + 1) / D)) := by rwa [measure_congr hae]
  exact nonempty_of_measure_ne_zero hpos'.ne'

/-- Positive-duration marks suffice; isolated or null time slices need not
be made part of a measurable existential-projection mark set. -/
theorem duration_le_positiveTimeMarks {α : Type*} {D : ℕ} (hD : 1 ≤ D)
    (E : Set (α × ℝ)) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (x : α) :
    incidenceDuration E x ≤ ENNReal.ofReal
      (((positiveTimeMarks D E x).card : ℝ) / (D : ℝ)) := by
  classical
  let J := positiveTimeMarks D E x
  have hcover : Prod.mk x ⁻¹' E ⊆
      ⋃ j : Fin D, ((Prod.mk x ⁻¹' E) ∩ timeCell D j) := by
    intro t ht
    obtain ⟨j, hj⟩ := exists_timeCell hD (hunit ht).2
    exact mem_iUnion.mpr ⟨j, ht, hj⟩
  have hcell (j : Fin D) : volume (timeCell D j) = ENNReal.ofReal (1 / (D : ℝ)) := by
    rw [timeCell, Real.volume_Icc]
    congr 1
    ring
  calc
    incidenceDuration E x ≤
        ∑ j : Fin D, volume ((Prod.mk x ⁻¹' E) ∩ timeCell D j) :=
      (measure_mono hcover).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ j : Fin D, if j ∈ J then ENNReal.ofReal (1 / (D : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ J
      · rw [ite_eq_left hj]
        exact (measure_mono inter_subset_right).trans_eq (hcell j)
      · rw [ite_eq_right hj]
        have hzero : volume ((Prod.mk x ⁻¹' E) ∩ timeCell D j) = 0 := by
          apply le_antisymm _ zero_le
          exact le_of_not_gt (fun hp => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
        exact hzero.le
    _ = (J.card : ℝ≥0∞) * ENNReal.ofReal (1 / (D : ℝ)) := by
      simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((J.card : ℝ) / (D : ℝ)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

theorem positiveTimeMarks_card_lower {α : Type*} {D : ℕ} (hD : 1 ≤ D)
    (E : Set (α × ℝ)) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) (x : α)
    {τ : ℝ} (hτ : 0 ≤ τ) (hduration : ENNReal.ofReal τ ≤ incidenceDuration E x) :
    (D : ℝ) * τ ≤ ((positiveTimeMarks D E x).card : ℝ) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have h := hduration.trans (duration_le_positiveTimeMarks hD E hunit x)
  have hreal : τ ≤ ((positiveTimeMarks D E x).card : ℝ) / (D : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hmul := (le_div_iff₀ hDpos).mp hreal
  simpa only [mul_comm] using hmul

end Submission.Obl.k4_initial_horizon_bound
