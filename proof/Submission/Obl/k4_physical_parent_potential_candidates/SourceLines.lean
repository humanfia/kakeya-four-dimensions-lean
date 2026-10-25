import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalSource
import Submission.Obl.k4_physical_parent_potential_candidates.PositiveFibers
import Submission.Obl.k4_physical_parent_potential_candidates.GroupFamily

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open scoped ENNReal

noncomputable section

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln} {B a ζ d : ℝ} {c u : P2} {P0 : Po}
  {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

def lineSet : Set Ln := positiveSourceLines source.S

def positiveEvents : Set Ev := source.S ∩ Prod.fst ⁻¹' source.lineSet

theorem measurable_lineSet : MeasurableSet source.lineSet :=
  measurableSet_positiveSourceLines source.S source.measurable_S

theorem measurable_positiveEvents : MeasurableSet source.positiveEvents :=
  source.measurable_S.inter (source.measurable_lineSet.preimage measurable_fst)

theorem positive_events_subset : source.positiveEvents ⊆ source.S := inter_subset_left

theorem positive_events_law [IsFiniteMeasure ν] :
    (ν.prod volume).restrict source.positiveEvents = (ν.prod volume).restrict source.S :=
  restrict_source_positive_lines ν source.S source.measurable_S

theorem lineSet_subset (hSA : ∀ e ∈ source.S, e.1 ∈ A) : source.lineSet ⊆ A :=
  positiveSourceLines_subset source.S A hSA

theorem positive_events_support
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹)) :
    source.positiveEvents ⊆ source.lineSet ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹) :=
  fun e he => ⟨he.2, (hSA he.1).2⟩

theorem line_velocity (l : Ln) (hl : l ∈ source.lineSet) : ‖v l‖ ≤ source.K := by
  obtain ⟨t, ht⟩ := exists_source_event_of_positive_line hl
  exact (source.point_bounds (l,t) ht).2.1

theorem line_origin
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    (l : Ln) (hl : l ∈ source.lineSet) : ‖packetOrigin T j c u l‖ ≤ 3*source.K := by
  obtain ⟨t, ht⟩ := exists_source_event_of_positive_line hl
  have htime := (hSA ht).2
  have ht' : t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹) := by
    exact ⟨htime.1, by nlinarith [htime.2]⟩
  exact packetOrigin_bound (by linarith [source.K_two]) (l,t) ht'
    (source.point_bounds (l,t) ht).1 (source.point_bounds (l,t) ht).2.1

theorem line_jets (l : Ln) (hl : l ∈ source.lineSet) :
    ∀ t ∈ Icc (0:ℝ) 1,
      |eval (xp l t) P0| ≤ source.K ∧
      |eval (xp l t) (pderiv 3 P0)| ≤ source.K*B ∧
      |eval (xp l t) (pderiv 3 (pderiv 3 P0))| ≤ source.K*B^2 := by
  obtain ⟨t, ht⟩ := exists_source_event_of_positive_line hl
  exact (source.point_bounds (l,t) ht).2.2.1

theorem line_fit (l : Ln) (hl : l ∈ source.lineSet) :
    ∀ t ∈ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹),
      |(eval (xp l t) P0 - eval (fun i => packetBase T j c u (l,t) i) source.Pot) -
        ownIntercept T j c u P0 source.Pot l| ≤ a*ζ := by
  obtain ⟨t, ht⟩ := exists_source_event_of_positive_line hl
  exact (source.point_bounds (l,t) ht).2.2.2.2

theorem coordinate_bound (e : Ev) (he : e ∈ source.S) (i : Fin 3) :
    |packetBase T j c u e i| ≤ source.K := by
  simpa only [Real.norm_eq_abs] using
    (PiLp.norm_apply_le (packetBase T j c u e) i).trans (source.point_bounds e he).1

theorem fit_at_source_event
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    (e : Ev) (he : e ∈ source.S) :
    |(packetSignal P0 e - eval (fun i => packetBase T j c u e i) source.Pot) -
      ownIntercept T j c u P0 source.Pot e.1| ≤ a*ζ := by
  have htime := (hSA he).2
  exact (source.point_bounds e he).2.2.2.2 e.2 ⟨htime.1, by nlinarith [htime.2]⟩

theorem normalized_fit_at_source_event
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    (e : Ev) (he : e ∈ source.S) :
    |packetSignal P0 e/a -
      eval (fun i => packetBase T j c u e i) source.Pot/a -
      ownIntercept T j c u P0 source.Pot e.1/a| ≤ ζ :=
  normalized_own_fit source.a_pos (source.fit_at_source_event hSA e he)

theorem potential_lipschitz (e : Ev) (he : e ∈ source.S) (f : Ev) (hf : f ∈ source.S) :
    |eval (fun i => packetBase T j c u e i) source.Pot/a -
      eval (fun i => packetBase T j c u f i) source.Pot/a| ≤
    (physicalPotentialLip q source.K*((2:ℝ)^T)⁻¹/a) *
      ‖(fun i => packetBase T j c u e i) - (fun i => packetBase T j c u f i)‖ :=
  physical_potential_lipschitz q source.Pot source.degree
    (by linarith [source.K_two]) (by positivity) source.a_pos source.coeff
    _ _ (source.coordinate_bound e he) (source.coordinate_bound f hf)

theorem normalized_fit_at_event
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹))
    (e : Ev) (he : e ∈ source.positiveEvents) :
    |packetSignal P0 e/a -
      eval (fun i => packetBase T j c u e i) source.Pot/a -
      ownIntercept T j c u P0 source.Pot e.1/a| ≤ ζ := by
  apply normalized_own_fit source.a_pos
  have htime := (hSA he.1).2
  exact source.line_fit e.1 he.2 e.2 ⟨htime.1, by nlinarith [htime.2]⟩

include source in
theorem reference_prior_pos [IsFiniteMeasure ν] : 0 < ν.real A := by
  have hne : ν A ≠ 0 := by
    intro hz
    have hpos := source.reference_pos
    rw [hz, mul_zero] at hpos
    exact lt_irrefl _ hpos
  exact ENNReal.toReal_pos hne (measure_ne_top ν A)

theorem positive_events_mass_floor [IsFiniteMeasure ν]
    (hSA : source.S ⊆ A ×ˢ Icc ((j:ℝ)*((2:ℝ)^T)⁻¹)
      ((j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹)) :
    ((2:ℝ)^T)⁻¹*ν.real A/source.K ≤ (ν.prod volume).real source.positiveEvents := by
  have hfinite : ((ν.prod volume).restrict source.S) univ ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (b := ENNReal.ofReal (((2:ℝ)^T)⁻¹)*ν A) (by finiteness)
    exact original_block_mass_le ν A ((j:ℝ)*((2:ℝ)^T)⁻¹) ((2:ℝ)^T)⁻¹ source.S hSA
  have hr := ENNReal.toReal_mono hfinite source.mass_floor
  have hclock : 0 ≤ ((2:ℝ)^T)⁻¹ := by positivity
  have hK : 0 ≤ source.K := by linarith [source.K_two]
  have heq : (ν.prod volume).real source.positiveEvents = (ν.prod volume).real source.S := by
    have hh := congrArg (fun μ : Measure Ev => μ.real univ) source.positive_events_law
    simpa only [measureReal_def, Measure.restrict_apply_univ] using hh
  rw [heq]
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hclock, ENNReal.toReal_ofReal hK,
    measureReal_def, Measure.restrict_apply_univ] using hr

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
