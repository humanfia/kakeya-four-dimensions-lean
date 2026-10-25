import Submission.Obl.k4_oss_collision_cauchy_schwarz.Arithmetic
import Mathlib

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_paired_full_time_binning

noncomputable section

/-- Fubini with the reference time placed outside both trajectory and current time. -/
lemma pair_fubini {α : Type} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {S : Set (α × (ℝ × ℝ))} (hS : MeasurableSet S) :
    (ν.prod (volume.prod volume)) S =
      ∫⁻ t : ℝ, (ν.prod volume) {p : α × ℝ | (p.1, (t, p.2)) ∈ S} := by
  have hSm : MeasurableSet {p : (α × ℝ) × ℝ | (p.1.1, (p.1.2, p.2)) ∈ S} :=
    hS.preimage (by fun_prop)
  have hf : Measurable (fun p : α × ℝ =>
      volume {t : ℝ | (p.1, (p.2, t)) ∈ S}) := measurable_measure_prodMk_left hSm
  rw [Measure.prod_apply hS]
  simp_rw [Measure.prod_apply (measurable_prodMk_left hS)]
  rw [lintegral_lintegral_swap hf.aemeasurable]
  apply lintegral_congr
  intro t
  have htS : MeasurableSet {p : α × ℝ | (p.1, (t, p.2)) ∈ S} :=
    hS.preimage (show Measurable (fun p : α × ℝ => (p.1, (t, p.2))) by fun_prop)
  exact (Measure.prod_apply htS).symm

lemma pair_mass_sq {α : Type} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    (ν.prod volume) E * (ν.prod volume) E ≤
      (ν.prod (volume.prod volume))
        {p : α × (ℝ × ℝ) | (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E} := by
  have hP : MeasurableSet {p : α × (ℝ × ℝ) |
      (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E} :=
    (hE.preimage (by fun_prop)).inter (hE.preimage (by fun_prop))
  rw [Measure.prod_apply hE, Measure.prod_apply hP]
  change (∫⁻ a, volume {t : ℝ | (a, t) ∈ E} ∂ν) *
      (∫⁻ a, volume {t : ℝ | (a, t) ∈ E} ∂ν) ≤
    ∫⁻ a, (volume.prod volume) ({t : ℝ | (a, t) ∈ E} ×ˢ {t : ℝ | (a, t) ∈ E}) ∂ν
  simp_rw [Measure.prod_prod]
  exact Submission.Obl.k4_oss_collision_cauchy_schwarz.lintegral_mul_self_le ν
    (measurable_measure_prodMk_left hE)

/-- A small exceptional pair mass leaves a time slice carrying a quadratic mass floor. -/
lemma select_time {α : Type} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hEI : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {R : Set (α × (ℝ × ℝ))} (hR : MeasurableSet R)
    (hp : 0 < ((ν.prod volume).restrict E) univ)
    (hbad : (ν.prod (volume.prod volume))
      {p : α × (ℝ × ℝ) | (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E ∧ p ∉ R} ≤
      ENNReal.ofReal ((((ν.prod volume).restrict E).real univ) ^ 2 / 4)) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal ((((ν.prod volume).restrict E).real univ) ^ 2 / 4) ≤
        ((ν.prod volume).restrict E)
          {p : α × ℝ | (p.1, t) ∈ E ∧ (p.1, (t, p.2)) ∈ R} := by
  classical
  let μ := (ν.prod volume).restrict E
  let pair := ν.prod (volume.prod volume : Measure (ℝ × ℝ))
  let P : Set (α × (ℝ × ℝ)) :=
    {p | (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E}
  let S := P ∩ R
  let q := ENNReal.ofReal ((μ.real univ) ^ 2 / 4)
  have hP : MeasurableSet P :=
    (hE.preimage (by fun_prop)).inter (hE.preimage (by fun_prop))
  have hS : MeasurableSet S := hP.inter hR
  have hfin : (ν.prod volume) E ≠ ⊤ := by
    have hle : (ν.prod volume) E ≤ 1 := by
      calc
        _ ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hEI
        _ = 1 := by simp
    exact ne_top_of_le_ne_top (by norm_num) hle
  have hp0 : 0 < (ν.prod volume) E := by simpa only [Measure.restrict_apply_univ] using hp
  have hreal : ENNReal.ofReal (μ.real univ) = (ν.prod volume) E := by
    simp only [μ, measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.ofReal_toReal hfin
  have hpReal : 0 < μ.real univ := by
    simp only [μ, measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos (ne_of_gt hp0) hfin
  by_contra hn
  have ht (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      μ {p : α × ℝ | (p.1, t) ∈ E ∧ (p.1, (t, p.2)) ∈ R} ≤ q := by
    exact le_of_lt (lt_of_not_ge (fun hh => hn ⟨t, ht, hh⟩))
  have hslice (t : ℝ) :
      (ν.prod volume) {p : α × ℝ | (p.1, (t, p.2)) ∈ S} =
        μ {p : α × ℝ | (p.1, t) ∈ E ∧ (p.1, (t, p.2)) ∈ R} := by
    have hslice : MeasurableSet {p : α × ℝ | (p.1, t) ∈ E ∧
        (p.1, (t, p.2)) ∈ R} :=
      (hE.preimage (by fun_prop)).inter (hR.preimage (by fun_prop))
    change (ν.prod volume) _ = ((ν.prod volume).restrict E) _
    rw [Measure.restrict_apply hslice]
    congr 1
    ext p
    simp [S, P, and_assoc, and_left_comm, and_comm]
  have hgood : pair S ≤ q := by
    change (ν.prod (volume.prod volume)) S ≤ q
    rw [pair_fubini ν hS]
    calc
      _ ≤ ∫⁻ t : ℝ, (Icc (0 : ℝ) 1).indicator (fun _ => q) t := by
        apply lintegral_mono
        intro t
        dsimp only
        rw [hslice]
        by_cases htI : t ∈ Icc (0 : ℝ) 1
        · simpa only [Set.indicator_of_mem htI] using ht t htI
        · rw [Set.indicator_of_notMem htI]
          have hempty : {p : α × ℝ | (p.1, t) ∈ E ∧ (p.1, (t, p.2)) ∈ R} = ∅ := by
            ext p
            simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
            intro hpE
            exact fun _ => htI (hEI hpE).2
          rw [hempty, measure_empty]
      _ = q := by rw [lintegral_indicator_const measurableSet_Icc]; simp
  have htotal : pair P ≤ q + q := by
    calc
      _ ≤ pair S + pair (P \ R) := by
        have hcover : P ⊆ S ∪ (P \ R) := by
          intro p hpP
          by_cases hpR : p ∈ R
          · exact Or.inl ⟨hpP, hpR⟩
          · exact Or.inr ⟨hpP, hpR⟩
        exact (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ q + q := add_le_add hgood (by
        rw [show P \ R = {p : α × (ℝ × ℝ) |
          (p.1, p.2.1) ∈ E ∧ (p.1, p.2.2) ∈ E ∧ p ∉ R} by
            ext p
            simp [P, and_assoc]]
        exact hbad)
  have hsquare : ENNReal.ofReal ((μ.real univ) ^ 2) ≤ q + q := by
    rw [pow_two, ENNReal.ofReal_mul hpReal.le, hreal]
    exact (pair_mass_sq ν hE).trans htotal
  have hstrict : q + q < ENNReal.ofReal ((μ.real univ) ^ 2) := by
    dsimp only [q]
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (μ.real univ) ^ 2 / 4)
      (by positivity : 0 ≤ (μ.real univ) ^ 2 / 4)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith [sq_pos_of_pos hpReal])
  exact (not_le_of_gt hstrict) hsquare

end

end Submission.Obl.k4_paired_full_time_binning
