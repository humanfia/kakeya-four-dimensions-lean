-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.LipschitzCoarseDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/LipschitzCoarseDuration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/LipschitzCoarseDuration.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CoarseDuration
import Submission.Obl.k4_scalar_grid_parameter_preparation.CurveCells
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSlopeDuration

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Set MeasureTheory SourceGeometry
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_graph_residual_discovery
open scoped ENNReal

noncomputable section

/-- A coordinate Lipschitz bound gives a finite visited-cell menu,
independently of every constant coordinate offset. -/
theorem exists_lipschitz_curve_cell_menu (F : ℝ → Fin 4 → ℝ) {K q : ℝ}
    (hK : 0 ≤ K) (hq : 0 < q)
    (hLip : ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (0:ℝ) 1, ∀ j,
      |F s j-F t j| ≤ K*|s-t|) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card:ℝ) ≤ (K/q+3)*(7:ℝ)^4 ∧
      ∀ c, c∈S ↔ ∃ t∈Icc (0:ℝ) 1, (fun j => ⌊F t j/q⌋)=c := by
  classical
  let D := ⌈K/q⌉₊+1
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hscale : K ≤ (D:ℝ)*q := by
    apply (div_le_iff₀ hq).mp
    have hh := Nat.le_ceil (K/q)
    dsimp [D]
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  obtain ⟨Q,hQ,hcover⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_curve_grid_cover F hK hq D hD hscale hLip
  let S := Q.filter (fun c => ∃ t∈Icc (0:ℝ) 1, (fun j => ⌊F t j/q⌋)=c)
  have hDupper : (D:ℝ)+1 ≤ K/q+3 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hK hq.le)).le
    dsimp [D]
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  refine ⟨S,?_,?_⟩
  · calc
      (S.card:ℝ) ≤ (Q.card:ℝ) := by exact_mod_cast Finset.card_filter_le Q _
      _ ≤ ((D:ℝ)+1)*(7:ℝ)^4 := hQ
      _ ≤ (K/q+3)*(7:ℝ)^4 := mul_le_mul_of_nonneg_right hDupper (by positivity)
  · intro c
    constructor
    · exact fun hc => (Finset.mem_filter.mp hc).2
    · rintro ⟨t,ht,rfl⟩
      exact Finset.mem_filter.mpr ⟨hcover t ht,t,ht,rfl⟩

def curveCoarseCode {X : Type*} (F : X → ℝ → Fin 4 → ℝ) (coarse : ℝ)
    (z : X × ℝ) : Fin 4 → ℤ := fun j => ⌊F z.1 z.2 j/coarse⌋

/-- The real-valued prior ceiling for any earlier measurable cell. Its
denominator is the duration threshold, and its numerator is the earlier
incidence mass under the same original prior. -/
theorem earlier_cell_duration_prior_cap_real {X I : Type*}
    [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure X) [IsFiniteMeasure ν] (E : Set (X × ℝ))
    (hE : MeasurableSet E) (hunit : E⊆univ ×ˢ Icc (0:ℝ) 1)
    (code : X × ℝ → I) (hcode : Measurable code) (q : I)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    (ν.restrict {x | ENNReal.ofReal threshold ≤
      incidenceDuration (E∩code ⁻¹' {q}) x}).real univ ≤
        ((ν.prod volume).restrict E).real (code ⁻¹' {q})/threshold := by
  let source := E∩code ⁻¹' {q}
  let long := {x | ENNReal.ofReal threshold ≤ incidenceDuration source x}
  let μ := (ν.prod volume).restrict E
  have hcell : MeasurableSet (code ⁻¹' {q}) := hcode (measurableSet_singleton q)
  have hsource : MeasurableSet source := hE.inter hcell
  have hlong : MeasurableSet long :=
    measurableSet_le measurable_const (measurable_incidenceDuration hsource)
  have hunitSource : source⊆univ ×ˢ Icc (0:ℝ) 1 := inter_subset_left.trans hunit
  have hμfinite : IsFiniteMeasure μ := by
    constructor
    change ((ν.prod volume).restrict E) univ < ∞
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ (ν.prod volume) (univ ×ˢ Icc (0:ℝ) 1) := measure_mono hunit
      _ = ν univ := by rw [Measure.prod_prod,Real.volume_Icc]; simp
      _ < ∞ := measure_lt_top ν univ
  letI := hμfinite
  have hcap : (ν.prod volume).real (source∩(long ×ˢ univ)) ≤
      μ.real (code ⁻¹' {q}) := by
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    change (ν.prod volume) (source∩(long ×ˢ univ)) ≤
      ((ν.prod volume).restrict E) (code ⁻¹' {q})
    rw [Measure.restrict_apply hcell]
    apply measure_mono
    intro z hz
    exact ⟨hz.1.2,hz.1.1⟩
  have hh := Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar.original_prior_cap_of_duration
    ν hsource hunitSource hlong hthreshold (fun x hx => hx) hcap
  simpa only [measureReal_def,Measure.restrict_apply_univ] using hh

/-- Earlier duration witnesses and the full original-prior cap require
only trajectory variation. The pointwise bound is needed on lines with
an actual source incidence; a large constant signal coefficient costs
nothing. No current incidence mass is made into a new prior. -/
theorem exists_lipschitz_coarse_duration_source {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (F : X → ℝ → Fin 4 → ℝ) {K coarse lossRate : ℝ}
    (hK : 0 ≤ K) (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1) (hRate : 0 ≤ lossRate)
    (hcurve : Measurable (fun z : X × ℝ => F z.1 z.2))
    (E : Set (X × ℝ)) (hE : MeasurableSet E) (hunit : E⊆univ ×ˢ Icc (0:ℝ) 1)
    (hLip : ∀ z∈E, ∀ s∈Icc (0:ℝ) 1, ∀ t∈Icc (0:ℝ) 1, ∀ j,
      |F z.1 s j-F z.1 t j| ≤ K*|s-t|) :
    ∃ keep : Set (X × ℝ), MeasurableSet keep ∧ keep⊆E ∧
      (ν.prod volume) (E\keep) ≤
        ENNReal.ofReal (lossRate*(K+3)*(7:ℝ)^4)*ν univ ∧
      (∀ z∈keep, ENNReal.ofReal (lossRate*coarse) ≤
        incidenceDuration (E∩(curveCoarseCode F coarse) ⁻¹'
          {curveCoarseCode F coarse z}) z.1) ∧
      ∀ q : Fin 4 → ℤ, ENNReal.ofReal (lossRate*coarse)*
        ν {x | ENNReal.ofReal (lossRate*coarse) ≤
          incidenceDuration (E∩(curveCoarseCode F coarse) ⁻¹' {q}) x} ≤
            (ν.prod volume) (E∩(curveCoarseCode F coarse) ⁻¹' {q}) := by
  classical
  let code := curveCoarseCode F coarse
  have hcode : Measurable code := by
    apply measurable_pi_iff.mpr
    intro j
    exact Int.measurable_floor.comp (((measurable_pi_apply j).comp hcurve).div_const coarse)
  let cells (q : Fin 4 → ℤ) := E∩code ⁻¹' {q}
  have hcells (q : Fin 4 → ℤ) : MeasurableSet (cells q) :=
    hE.inter (hcode (measurableSet_singleton q))
  have hex (x : X) : ∃ S : Finset (Fin 4 → ℤ),
      (S.card:ℝ) ≤ (K/coarse+3)*(7:ℝ)^4 ∧
      ∀ t, (x,t)∈E → code (x,t)∈S := by
    by_cases hx : ∃ t, (x,t)∈E
    · obtain ⟨t,ht⟩ := hx
      obtain ⟨S,hS,hcover⟩ := exists_lipschitz_curve_cell_menu (F x) hK hcoarse (hLip (x,t) ht)
      exact ⟨S,hS,fun u hu => (hcover _).mpr ⟨u,(hunit hu).2,rfl⟩⟩
    · refine ⟨∅,by simp; positivity,?_⟩
      intro t ht
      exact (hx ⟨t,ht⟩).elim
  choose menus hmenus hcover using hex
  let a := ENNReal.ofReal (lossRate*coarse)
  let D := ENNReal.ofReal ((K/coarse+3)*(7:ℝ)^4)
  have hcount (x : X) : ((menus x).card:ENNReal) ≤ D := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hmenus x)
  have hsupport (x : X) (q : Fin 4 → ℤ) (hq : incidenceDuration (cells q) x ≠ 0) : q∈menus x := by
    obtain ⟨t,ht⟩ := nonempty_of_measure_ne_zero hq
    have hh := hcover x t ht.1
    exact ht.2 ▸ hh
  let bad := ⋃ q : Fin 4 → ℤ,
    cells q∩({x | incidenceDuration (cells q) x<a} ×ˢ (univ : Set ℝ))
  have hbad : MeasurableSet bad := by
    apply MeasurableSet.iUnion
    intro q
    exact (hcells q).inter ((measurableSet_lt
      (measurable_incidenceDuration (hcells q)) measurable_const).prod MeasurableSet.univ)
  have hraw : (ν.prod volume) bad ≤ a*D*ν univ := by
    simpa only [one_smul,one_mul] using counted_short_incidence_deletion_le ν
      (ν.prod volume) (c:=1) (by simp) hcells menus a D hcount hsupport
  have hnum : (lossRate*coarse)*((K/coarse+3)*(7:ℝ)^4) ≤
      lossRate*(K+3)*(7:ℝ)^4 := by
    have hh : coarse*(K/coarse+3) ≤ K+3 := by
      rw [mul_add,mul_div_cancel₀ _ hcoarse.ne']
      linarith
    calc
      _ = lossRate*(coarse*(K/coarse+3))*(7:ℝ)^4 := by ring
      _ ≤ lossRate*(K+3)*(7:ℝ)^4 := by gcongr
  have hbudget : a*D ≤ ENNReal.ofReal (lossRate*(K+3)*(7:ℝ)^4) := by
    rw [←ENNReal.ofReal_mul (mul_nonneg hRate hcoarse.le)]
    exact ENNReal.ofReal_le_ofReal hnum
  refine ⟨E\bad,hE.diff hbad,diff_subset,?_,?_,?_⟩
  · apply (measure_mono ?_).trans (hraw.trans (mul_le_mul' hbudget le_rfl))
    intro z hz
    by_contra h
    exact hz.2 ⟨hz.1,h⟩
  · intro z hz
    by_contra hh
    have hshort : incidenceDuration (cells (code z)) z.1<a := lt_of_not_ge hh
    exact hz.2 (mem_iUnion.mpr ⟨code z,⟨⟨hz.1,rfl⟩,hshort,mem_univ _⟩⟩)
  · intro q
    let long := {x | a ≤ incidenceDuration (cells q) x}
    have hlong : MeasurableSet long :=
      measurableSet_le measurable_const (measurable_incidenceDuration (hcells q))
    have hh := retained_duration_prior_bound ν (hcells q) MeasurableSet.univ hlong a
      (fun x hx => hx.2)
    rw [Measure.restrict_apply_univ,duration_withDensity_apply ν (hcells q) MeasurableSet.univ] at hh
    simpa only [univ_prod,preimage_univ,inter_univ] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
