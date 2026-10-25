import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.Analytic.GeneralPositionSampling

/-!
# Seven events of one broad cell (lane B, step 2)

Without a common palette the seven directions are chosen separately in every fine state. A
cell `S` of positive finite mass whose velocity law charges no strip of half-width `δ` by more
than `κ` of its mass, with `686 κ < 1`, contains seven events whose velocities have all triple
determinants at least `δ²`: independent draws from the cell's normalized law are in general
position with positive probability (`general_position_of_breadth`), and almost every draw is a
tuple of events of the cell.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MeasureTheory Set GeneralPositionSampling
open scoped ENNReal

/-- **Seven events of one broad cell in general position.** -/
theorem exists_seven_of_broad_cell {X : Type*} [MeasurableSpace X] (μ0 : Measure X)
    (S : Set X) (hS : MeasurableSet S) (hpos : μ0 S ≠ 0) (hfin : μ0 S ≠ ∞)
    (vel : X → EuclideanSpace ℝ (Fin 2)) (hvel : Measurable vel)
    {δ : ℝ} (hδ : 0 < δ) {κ : ℝ≥0∞} (hκ : 686 * κ < 1)
    (hb : ∀ (m : EuclideanSpace ℝ (Fin 2)) (c : ℝ), ‖m‖ = 1 →
      μ0 (S ∩ vel ⁻¹' {x | |inner ℝ m x - c| ≤ δ}) ≤ κ * μ0 S) :
    ∃ e : Fin 7 → X, (∀ i, e i ∈ S) ∧
      ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        δ ^ 2 ≤ |tripleDet (vel (e i)) (vel (e j)) (vel (e k))| := by
  classical
  set ρ : Measure X := (μ0 S)⁻¹ • μ0.restrict S with hρ
  have hρS : ρ S = 1 := by
    simp only [hρ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS, inter_self]
    exact ENNReal.inv_mul_cancel hpos hfin
  have hρuniv : ρ univ = 1 := by
    simp only [hρ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    exact ENNReal.inv_mul_cancel hpos hfin
  haveI : IsProbabilityMeasure ρ := ⟨hρuniv⟩
  set μ : Measure (EuclideanSpace ℝ (Fin 2)) := ρ.map vel with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; exact (Measure.isProbabilityMeasure_map_iff hvel.aemeasurable).mpr inferInstance
  have hbreadth : StripBreadth μ δ κ := by
    intro m c hm
    have hmeas : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | |inner ℝ m x - c| ≤ δ} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [hμ, Measure.map_apply hvel hmeas]
    simp only [hρ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hvel hmeas)]
    calc (μ0 S)⁻¹ * μ0 (vel ⁻¹' {x | |inner ℝ m x - c| ≤ δ} ∩ S)
        = (μ0 S)⁻¹ * μ0 (S ∩ vel ⁻¹' {x | |inner ℝ m x - c| ≤ δ}) := by rw [inter_comm]
      _ ≤ (μ0 S)⁻¹ * (κ * μ0 S) := by gcongr; exact hb m c hm
      _ = κ := by rw [mul_comm κ, ← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]
  have hbad := general_position_of_breadth μ hδ hbreadth 6
  set Bad : Set (Fin 7 → EuclideanSpace ℝ (Fin 2)) :=
    {v | ∃ i j k : Fin 7, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ |tripleDet (v i) (v j) (v k)| < δ ^ 2}
    with hBad
  have hdet : ∀ i j k : Fin 7, Continuous fun v : Fin 7 → EuclideanSpace ℝ (Fin 2) =>
      tripleDet (v i) (v j) (v k) := by
    intro i j k
    simp only [tripleDet_eq]
    fun_prop
  have hBadm : MeasurableSet Bad := by
    have : Bad = ⋃ i : Fin 7, ⋃ j : Fin 7, ⋃ k : Fin 7,
        {v : Fin 7 → EuclideanSpace ℝ (Fin 2) | i ≠ j ∧ i ≠ k ∧ j ≠ k} ∩
          {v | |tripleDet (v i) (v j) (v k)| < δ ^ 2} := by
      ext v
      simp only [hBad, mem_setOf_eq, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨i, j, k, hij, hik, hjk, h⟩
        exact ⟨i, j, k, ⟨hij, hik, hjk⟩, h⟩
      · rintro ⟨i, j, k, ⟨hij, hik, hjk⟩, h⟩
        exact ⟨i, j, k, hij, hik, hjk, h⟩
    rw [this]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun k => ?_
    by_cases hd : i ≠ j ∧ i ≠ k ∧ j ≠ k
    · have h1 : {v : Fin 7 → EuclideanSpace ℝ (Fin 2) | i ≠ j ∧ i ≠ k ∧ j ≠ k} = univ := by
        ext v; simp only [mem_setOf_eq, mem_univ, iff_true]; exact hd
      rw [h1, univ_inter]
      exact measurableSet_lt ((hdet i j k).abs).measurable measurable_const
    · have h1 : {v : Fin 7 → EuclideanSpace ℝ (Fin 2) | i ≠ j ∧ i ≠ k ∧ j ≠ k} = ∅ := by
        ext v; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]; exact hd
      rw [h1, empty_inter]
      exact MeasurableSet.empty
  set P7 : Measure (Fin 7 → X) := Measure.pi fun _ : Fin 7 => ρ with hP7
  set V : (Fin 7 → X) → (Fin 7 → EuclideanSpace ℝ (Fin 2)) := fun x i => vel (x i) with hV
  have hVm : Measurable V := measurable_pi_iff.mpr fun i => hvel.comp (measurable_pi_apply i)
  have hmap : P7.map V = Measure.pi fun _ : Fin 7 => μ :=
    Measure.pi_map_pi (fun _ => hvel.aemeasurable)
  have hlt : P7 (V ⁻¹' Bad) < 1 := by
    rw [← Measure.map_apply hVm hBadm, hmap]
    calc (Measure.pi fun _ : Fin 7 => μ) Bad ≤ 2 * ((6 + 1) ^ 3 : ℝ≥0∞) * κ := hbad
      _ = 686 * κ := by norm_num
      _ < 1 := hκ
  have hpiS : P7 (Set.pi univ fun _ : Fin 7 => S) = 1 := by
    rw [hP7, Measure.pi_pi]
    simp [hρS]
  haveI : IsProbabilityMeasure P7 := by rw [hP7]; infer_instance
  have hcompl : P7 (Set.pi univ fun _ : Fin 7 => S)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (MeasurableSet.univ_pi fun _ => hS)]
    exact hpiS
  have hne : (V ⁻¹' Bad ∪ (Set.pi univ fun _ : Fin 7 => S)ᶜ) ≠ univ := by
    intro heq
    have h1 : P7 (V ⁻¹' Bad ∪ (Set.pi univ fun _ : Fin 7 => S)ᶜ) < 1 :=
      calc P7 (V ⁻¹' Bad ∪ (Set.pi univ fun _ : Fin 7 => S)ᶜ)
          ≤ P7 (V ⁻¹' Bad) + P7 (Set.pi univ fun _ : Fin 7 => S)ᶜ := measure_union_le _ _
        _ = P7 (V ⁻¹' Bad) := by rw [hcompl, add_zero]
        _ < 1 := hlt
    rw [heq, measure_univ] at h1
    exact lt_irrefl _ h1
  obtain ⟨x, hx⟩ : ∃ x, x ∉ V ⁻¹' Bad ∪ (Set.pi univ fun _ : Fin 7 => S)ᶜ := by
    by_contra hall
    push Not at hall
    exact hne (eq_univ_of_forall hall)
  simp only [mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at hx
  obtain ⟨hgood, hin⟩ := hx
  refine ⟨x, fun i => hin i (mem_univ i), ?_⟩
  intro i j k hij hik hjk
  by_contra hlt'
  push Not at hlt'
  exact hgood ⟨i, j, k, hij, hik, hjk, hlt'⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
