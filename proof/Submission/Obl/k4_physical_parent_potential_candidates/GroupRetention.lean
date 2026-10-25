-- Adapted from this LOT tree, o286, branch x1021, commit 128bb7e2,
-- Submission/Obl/k4_native_field_original_candidates/GroupRetention.lean.
-- Original session x1021. Accepted helper results remain imported.
import Submission.Obl.k4_physical_parent_potential_candidates.InterceptState

open Set MeasureTheory

namespace Submission.Obl.k4_physical_parent_potential_candidates

/-- Read original fraction pruning in ordinary real mass units. -/
theorem group_fraction_keep_real_budget {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → I) (hstate : Measurable state)
    (S : Set Ω) (hS : MeasurableSet S) (group : Ω → ℤ) (hgroup : Measurable group)
    (menu : I → Finset ℤ) (M : ℕ) (hM : ∀ i, (menu i).card ≤ M)
    (hmenu : ∀ e ∈ S, group e ∈ menu (state e))
    (G : Finset ℤ) (hG : ∀ e ∈ S, group e ∈ G) (f : ℝ) (hf : 0 ≤ f) :
    μ.real S ≤ (∑ g ∈ G, μ.real (sourceGroupKeep μ state S group (ENNReal.ofReal f) g))+
      (M : ℝ)*f*μ.real univ := by
  have hh := (group_fraction_keep_budget μ state hstate S hS group hgroup menu M hM
    hmenu G hG (ENNReal.ofReal f)).2
  have hsumfin : (∑ g ∈ G, μ (sourceGroupKeep μ state S group (ENNReal.ofReal f) g)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top μ _)
  have hprod : (M : ENNReal)*ENNReal.ofReal f*μ univ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      (measure_ne_top μ univ)
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsumfin, hprod⟩) hh
  rw [ENNReal.toReal_add hsumfin hprod,
    ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hf, ENNReal.toReal_natCast,
    measureReal_def] using hr

/-- Short-line loss and a fixed original-state fraction deletion leave
at least a quarter of the original packet floor. -/
theorem quarter_reference_after_retention {K ref total long kept : ℝ}
    (hK : 2 ≤ K) (href : 0 ≤ ref) (hfloor : ref/K ≤ total)
    (hlong : total ≤ long+ref/K^2)
    (hkeep : long ≤ kept+(9/10000 : ℝ)*total) :
    ref/(4*K) ≤ kept := by
  have hKpos : 0 < K := by linarith
  have htotal : 0 ≤ total := (div_nonneg href hKpos.le).trans hfloor
  have hcost : ref/K^2 ≤ total/K := by
    simpa only [div_div, pow_two] using div_le_div_of_nonneg_right hfloor hKpos.le
  have hhalf : total/K ≤ total/2 := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith
  have hret : total/4 ≤ kept := by linarith
  have hh := div_le_div_of_nonneg_right hfloor (by norm_num : (0 : ℝ)≤4)
  exact (show ref/(4*K) ≤ total/4 by simpa only [div_div, mul_comm] using hh).trans hret

/-- Ratios on the original fine states pass to any assigned coarse cell
of a kept group, under its actual restricted original law. -/
theorem fraction_keep_coarse_event_ratio {Ω I B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (state : Ω → I) (hstate : Measurable state)
    (G : Set Ω) (hG : MeasurableSet G) {f : ENNReal} (hf0 : f ≠ 0) (hftop : f ≠ ⊤)
    (coarse : I → B) (b : B) (E : Set Ω) (hE : MeasurableSet E) (η : ENNReal)
    (hη : ∀ i, μ (state ⁻¹' {i} ∩ E) ≤ η*μ (state ⁻¹' {i})) :
    (μ.restrict (Submission.Lib.K4StateFractionKeep.fractionKeep μ state G f))
      {x | coarse (state x) = b ∧ x ∈ E} ≤
      (η/f)*(μ.restrict (Submission.Lib.K4StateFractionKeep.fractionKeep μ state G f))
        {x | coarse (state x) = b} := by
  have hU : MeasurableSet {x | coarse (state x) = b} :=
    hstate (Set.to_countable {i | coarse i = b}).measurableSet
  have hUE : MeasurableSet {x | coarse (state x) = b ∧ x ∈ E} := hU.inter hE
  rw [Measure.restrict_apply hUE, Measure.restrict_apply hU]
  have hh := Submission.Lib.K4StateFractionKeep.fractionKeep_union_ratio μ hstate hG
    hf0 hftop hE η hη {i | coarse i = b}
  have hleft : {x | coarse (state x) = b ∧ x ∈ E} ∩
      Submission.Lib.K4StateFractionKeep.fractionKeep μ state G f =
      Submission.Lib.K4StateFractionKeep.fractionKeep μ state G f ∩
        state ⁻¹' {i | coarse i = b} ∩ E := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage]
    tauto
  have hright : {x | coarse (state x) = b} ∩
      Submission.Lib.K4StateFractionKeep.fractionKeep μ state G f =
      Submission.Lib.K4StateFractionKeep.fractionKeep μ state G f ∩
        state ⁻¹' {i | coarse i = b} := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage]
    tauto
  rw [hleft, hright]
  exact hh

end Submission.Obl.k4_physical_parent_potential_candidates
