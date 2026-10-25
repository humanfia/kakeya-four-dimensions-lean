import Submission.Obl.k4_horizon_chart_assembly.Packets
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.TimeCells

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

def timeLift {α : Type*} (s q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, s + q * p.2)

theorem measurable_timeLift {α : Type*} [MeasurableSpace α] (s q : ℝ) :
    Measurable (timeLift (α := α) s q) := by
  fun_prop [timeLift]

def normalizedEvent {α : Type*} (E : Set (α × ℝ)) (s q : ℝ) : Set (α × ℝ) :=
  (univ ×ˢ Ico (0 : ℝ) 1) ∩ timeLift s q ⁻¹' E

theorem normalizedEvent_measurable {α : Type*} [MeasurableSpace α]
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (s q : ℝ) :
    MeasurableSet (normalizedEvent E s q) :=
  (MeasurableSet.univ.prod measurableSet_Ico).inter (hE.preimage (measurable_timeLift s q))

/-- The only Jacobian in normalization is the length of the time block. -/
theorem map_timeLift_prod {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (s : ℝ) {q : ℝ} (hq : 0 < q) :
    (ν.prod (volume : Measure ℝ)).map (timeLift s q) =
      ENNReal.ofReal q⁻¹ • (ν.prod volume) := by
  have hmap : (volume : Measure ℝ).map (fun t => s + q * t) =
      ENNReal.ofReal q⁻¹ • volume := by
    have hcomp : (fun t : ℝ => s + q * t) = (s + ·) ∘ (q * ·) := rfl
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      Real.map_volume_mul_left hq.ne', Measure.map_smul _ (by fun_prop),
      Measure.IsAddLeftInvariant.map_add_left_eq_self]
    rw [abs_of_pos (inv_pos.mpr hq)]
  have hprod := Measure.map_prod_map (f := id) (g := fun t : ℝ => s + q * t)
    ν volume measurable_id (by fun_prop)
  change (ν.map id).prod (volume.map (fun t : ℝ => s + q * t)) =
    (ν.prod volume).map (timeLift s q) at hprod
  simpa only [Measure.map_id, hmap, Measure.prod_smul_right] using hprod.symm

/-- A normalized original-law incidence mass becomes exactly the corresponding
physical block mass on the same trajectory assignment. -/
theorem normalized_incidence_mass {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    {A : Set α} (hA : MeasurableSet A) (s : ℝ) {q : ℝ} (hq : 0 < q) :
    ENNReal.ofReal q * (ν.prod volume) (normalizedEvent E s q ∩ (A ×ˢ univ)) =
      (ν.prod volume) (E ∩ (A ×ˢ Ico s (s + q))) := by
  have hm : MeasurableSet (E ∩ (A ×ˢ Ico s (s + q))) := hE.inter (hA.prod measurableSet_Ico)
  have heq : normalizedEvent E s q ∩ (A ×ˢ univ) =
      timeLift s q ⁻¹' (E ∩ (A ×ˢ Ico s (s + q))) := by
    ext p
    simp only [normalizedEvent, timeLift, mem_inter_iff, mem_preimage, mem_prod,
      mem_univ, true_and, and_true, mem_Ico]
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, hE⟩, hA⟩
      exact ⟨hE, hA, by nlinarith, by nlinarith⟩
    · rintro ⟨hE, hA, h0, h1⟩
      exact ⟨⟨⟨by nlinarith, by nlinarith⟩, hE⟩, hA⟩
  rw [heq, ← Measure.map_apply (measurable_timeLift s q) hm, map_timeLift_prod ν s hq,
    Measure.smul_apply, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hq.le,
    mul_inv_cancel₀ hq.ne', ENNReal.ofReal_one, one_mul]

/-- The half-open equal time blocks partition all original incidence mass on
`[0,1]`, since the final endpoint has zero product measure. -/
theorem sum_block_incidence {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {J : ℕ} (hJ : 0 < J) :
    (∑ j : Fin J, (ν.prod volume) (E ∩ (univ ×ˢ
      Submission.Obl.k4_scalar_marked_coefficient_smoothing.timeCell J j))) =
      (ν.prod volume) E := by
  let I := Submission.Obl.k4_scalar_marked_coefficient_smoothing.timeCell J
  have hI := Submission.Obl.k4_scalar_marked_coefficient_smoothing.timeCell_disjoint hJ
  have hM (j : Fin J) : MeasurableSet (univ ×ˢ I j : Set (α × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have hdisj : Pairwise (fun j j' => Disjoint (E ∩ (univ ×ˢ I j)) (E ∩ (univ ×ˢ I j'))) := by
    intro j j' hne
    exact ((Set.disjoint_left.mpr (fun p hp hp' => Set.disjoint_left.mp (hI hne) hp.2 hp'.2)) :
      Disjoint (univ ×ˢ I j : Set (α × ℝ)) (univ ×ˢ I j')).mono inter_subset_right inter_subset_right
  have hsum : (∑ j : Fin J, (ν.prod volume) (E ∩ (univ ×ˢ I j))) =
      (ν.prod volume) (E ∩ (univ ×ˢ Ico (0 : ℝ) 1)) := by
    have h := measure_iUnion (μ := ν.prod volume) hdisj (fun j => hE.inter (hM j))
    simpa only [tsum_fintype, ← inter_iUnion, ← prod_iUnion, I,
      Submission.Obl.k4_scalar_marked_coefficient_smoothing.iUnion_timeCell hJ] using h.symm


  rw [hsum]
  apply measure_congr
  have hnull : (ν.prod volume) (univ ×ˢ ({1} : Set ℝ)) = 0 := by simp [Measure.prod_prod]
  have hae : ∀ᵐ p : α × ℝ ∂ν.prod volume, p.2 ≠ 1 := by
    rw [ae_iff]
    have heq : {p : α × ℝ | ¬p.2 ≠ 1} = univ ×ˢ ({1} : Set ℝ) := by
      ext p
      simp
    rw [heq]
    exact hnull
  filter_upwards [hae] with p hp1
  simp only [mem_inter_iff, mem_prod, mem_univ, true_and, mem_Ico]
  apply propext
  constructor
  · exact And.left
  · intro hpE
    exact ⟨hpE, (hunit hpE).2.1, lt_of_le_of_ne (hunit hpE).2.2 hp1⟩

end
end Submission.Obl.k4_horizon_chart_assembly
