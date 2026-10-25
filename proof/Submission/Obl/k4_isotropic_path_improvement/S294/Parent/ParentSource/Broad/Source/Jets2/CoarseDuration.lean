-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.CoarseDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/CoarseDuration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/CoarseDuration.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.CoarseGeometry
import Submission.Obl.k4_scalar_graph_residual_discovery.CountedDuration

/-! # Earlier coarse-duration witnesses for physical coefficient curves

The counting argument is adapted from this obligation's
Broad/Velocity/CoarseDuration.lean. The cell menu here uses the four
bounded jets and permits arbitrary signal and spatial intercepts.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open MeasureTheory Set
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_graph_residual_discovery
open scoped ENNReal
noncomputable section

/-- Short portions are deleted against the unchanged trajectory prior.
Every later source may use the retained earlier duration witness. -/
theorem exists_coefficient_coarse_duration_source {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [SFinite ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    {H coarse lossRate : ℝ} (hH : 1≤H) (hcoarse : 0<coarse)
    (hcoarse1 : coarse≤1) (hRate : 0≤lossRate)
    (hjets : ∀ l, |c l 1|≤H ∧ |c l 2|≤H ∧ |c l 4|≤H ∧ |c l 6|≤H)
    (E : Set (Λ×ℝ)) (hE : MeasurableSet E) (hunit : E⊆univ×ˢ Icc (0:ℝ) 1) :
    let code := coefficientGridCode c coarse coarse
    ∃ keep : Set (Λ×ℝ), MeasurableSet keep ∧ keep⊆E ∧
      (ν.prod volume) (E\keep)≤
        ENNReal.ofReal (5*lossRate*(6*H+5)^4)*ν univ ∧
      (∀ z∈keep, ENNReal.ofReal (lossRate*coarse)≤
        incidenceDuration (E∩code ⁻¹' {code z}) z.1) ∧
      ∀ q : Fin 4 → ℤ,
        ENNReal.ofReal (lossRate*coarse)*ν
          {l | ENNReal.ofReal (lossRate*coarse) ≤ incidenceDuration (E∩code ⁻¹' {q}) l}≤
            (ν.prod volume) (E∩code ⁻¹' {q}) := by
  classical
  intro code
  have hcode : Measurable code := measurable_coefficientGridCode hc coarse coarse
  let cells (q : Fin 4 → ℤ) := E∩code ⁻¹' {q}
  have hcells (q : Fin 4 → ℤ) : MeasurableSet (cells q) :=
    hE.inter (hcode (measurableSet_singleton q))
  choose menus hmenus hcover using fun l =>
    exists_coefficient_curve_cell_menu hH hcoarse (c l)
      (hjets l).1 (hjets l).2.1 (hjets l).2.2.1 (hjets l).2.2.2
  let a := ENNReal.ofReal (lossRate*coarse)
  let D := ENNReal.ofReal ((2/coarse+3)*(6*H+5)^4)
  have hcount (l : Λ) : ((menus l).card : ENNReal)≤D := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hmenus l)
  have hsupport (l : Λ) (q : Fin 4 → ℤ) (hq : incidenceDuration (cells q) l≠0) :
      q∈menus l := by
    obtain ⟨t,ht⟩ := nonempty_of_measure_ne_zero hq
    apply (hcover l q).mpr
    refine ⟨t,(hunit ht.1).2,?_⟩
    have hq' : code (l,t)=q := ht.2
    apply funext
    intro j
    have hj := congrFun hq' j
    change ⌊coefficientPhysical (c l) t j/(if j=3 then coarse else coarse)⌋=q j at hj
    simpa only [ite_self] using hj
  let bad := ⋃ q : Fin 4 → ℤ,
    cells q∩({l | incidenceDuration (cells q) l<a}×ˢ (univ : Set ℝ))
  have hbad : MeasurableSet bad := by
    apply MeasurableSet.iUnion
    intro q
    exact (hcells q).inter ((measurableSet_lt
      (measurable_incidenceDuration (hcells q)) measurable_const).prod MeasurableSet.univ)
  have hraw : (ν.prod volume) bad≤a*D*ν univ := by
    simpa only [one_smul,one_mul] using counted_short_incidence_deletion_le ν
      (ν.prod volume) (c := 1) (by simp) hcells menus a D hcount hsupport
  have hnum : (lossRate*coarse)*((2/coarse+3)*(6*H+5)^4)≤
      5*lossRate*(6*H+5)^4 := by
    have hh : coarse*(2/coarse+3)≤5 := by
      rw [mul_add,mul_div_cancel₀ _ hcoarse.ne']
      linarith
    calc
      _ = lossRate*(coarse*(2/coarse+3))*(6*H+5)^4 := by ring
      _ ≤ lossRate*5*(6*H+5)^4 := by gcongr
      _ = _ := by ring
  have hbudget : a*D≤ENNReal.ofReal (5*lossRate*(6*H+5)^4) := by
    rw [←ENNReal.ofReal_mul (mul_nonneg hRate hcoarse.le)]
    exact ENNReal.ofReal_le_ofReal hnum
  refine ⟨E\bad,hE.diff hbad,diff_subset,?_,?_,?_⟩
  · apply (measure_mono ?_).trans (hraw.trans (mul_le_mul' hbudget le_rfl))
    intro z hz
    by_contra hh
    exact hz.2 ⟨hz.1,hh⟩
  · intro z hz
    by_contra hh
    have hshort : incidenceDuration (cells (code z)) z.1<a := lt_of_not_ge hh
    exact hz.2 (mem_iUnion.mpr ⟨code z,⟨⟨hz.1,rfl⟩,hshort,mem_univ _⟩⟩)
  · intro q
    let long := {l | a ≤ incidenceDuration (cells q) l}
    have hlong : MeasurableSet long :=
      measurableSet_le measurable_const (measurable_incidenceDuration (hcells q))
    have hh := retained_duration_prior_bound ν (hcells q) MeasurableSet.univ hlong a
      (fun l hl => hl.2)
    rw [Measure.restrict_apply_univ,duration_withDensity_apply ν (hcells q) MeasurableSet.univ] at hh
    simpa only [univ_prod,preimage_univ,inter_univ] using hh

/-- The duration-retained prior is still a restriction of the original
prior. Its cap uses the earlier cell mass, before any later deletion. -/
theorem coefficient_duration_prior_cap {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ×ℝ)) (hE : MeasurableSet E) (hunit : E⊆univ×ˢ Icc (0:ℝ) 1)
    {coarse lossRate : ℝ} (hcoarse : 0<coarse) (hRate : 0<lossRate) (q : Fin 4 → ℤ) :
    let code := coefficientGridCode c coarse coarse
    (ν.restrict {l | ENNReal.ofReal (lossRate*coarse)≤
      incidenceDuration (E∩code ⁻¹' {q}) l}).real univ≤
        ((ν.prod volume).restrict E).real (code ⁻¹' {q})/(lossRate*coarse) := by
  intro code
  let cells := E∩code ⁻¹' {q}
  have hcell : MeasurableSet (code ⁻¹' {q}) :=
    (measurable_coefficientGridCode hc coarse coarse) (measurableSet_singleton q)
  have hcells : MeasurableSet cells := hE.inter hcell
  let a := ENNReal.ofReal (lossRate*coarse)
  let long := {l | a ≤ incidenceDuration cells l}
  have hlong : MeasurableSet long :=
    measurableSet_le measurable_const (measurable_incidenceDuration hcells)
  have hh := retained_duration_prior_bound ν hcells MeasurableSet.univ hlong a
    (fun l hl => hl.2)
  rw [Measure.restrict_apply_univ,duration_withDensity_apply ν hcells MeasurableSet.univ] at hh
  simp only [univ_prod,preimage_univ,inter_univ] at hh
  let μ := (ν.prod volume).restrict E
  have hfinite : IsFiniteMeasure μ := by
    constructor
    rw [Measure.restrict_apply_univ]
    apply lt_of_le_of_lt (measure_mono hunit)
    rw [Measure.prod_prod,Real.volume_Icc]
    simp only [sub_zero,ENNReal.ofReal_one,mul_one]
    exact measure_lt_top ν univ
  have hmass : (ν.prod volume) cells=μ (code ⁻¹' {q}) := by
    rw [Measure.restrict_apply hcell,inter_comm]
  rw [hmass] at hh
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hh
  simp only [measureReal_def,Measure.restrict_apply_univ]
  apply (le_div_iff₀ (mul_pos hRate hcoarse)).mpr
  have hreal' : (lossRate*coarse)*(ν long).toReal≤(μ (code ⁻¹' {q})).toReal := by
    simpa only [a,ENNReal.toReal_mul,ENNReal.toReal_ofReal (mul_pos hRate hcoarse).le] using hreal
  nlinarith only [hreal']

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
