-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.Quantiles.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-! Quantile cuts for the stem-selection argument. The continuous-distribution
construction is adapted from x0528/o197 MeasureCut in this workspace. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal

/-- A bounded real coordinate with null level sets cuts a finite measure
continuously to any requested mass. -/
theorem exists_coordinate_cut {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E : Set X} (hEm : MeasurableSet E) (hEfin : μ E ≠ ∞)
    (f : X → ℝ) (hf : Measurable f) (hlevel : ∀ t, μ (f ⁻¹' {t}) = 0)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ p ∈ E, |f p| < B)
    {q : ENNReal} (hq : q ≤ μ E) :
    ∃ t : ℝ, t ∈ Icc (-B) B ∧ μ (E ∩ {p | f p ≤ t}) = q := by
  let ν : Measure ℝ := (μ.restrict E).map f
  letI : IsFiniteMeasure (μ.restrict E) := isFiniteMeasure_restrict.mpr hEfin
  letI : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure ((μ.restrict E).map f))
  letI : NullSingletonClass ν := ⟨fun t => by
    change (μ.restrict E).map f {t} = 0
    rw [Measure.map_apply hf (measurableSet_singleton t),
      Measure.restrict_apply ((measurableSet_singleton t).preimage hf)]
    exact measure_mono_null inter_subset_left (hlevel t)⟩
  have hcut (t : ℝ) : ν (Iic t) = μ (E ∩ {p | f p ≤ t}) := by
    rw [Measure.map_apply hf measurableSet_Iic,
      Measure.restrict_apply (measurableSet_Iic.preimage hf), inter_comm]
    rfl
  have hleft : E ∩ {p | f p ≤ -B} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, hpf⟩
    exact (not_le.mpr (abs_lt.mp (hbound p hp)).1) hpf
  have hright : E ∩ {p | f p ≤ B} = E :=
    inter_eq_left.mpr (fun p hp => (abs_lt.mp (hbound p hp)).2.le)
  have hcont : ContinuousOn (fun t : ℝ => (ν (Iic t)).toReal) (Icc (-B) B) := by
    have hint : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic B) ν :=
      (integrable_const (1 : ℝ)).integrableOn
    have hc := hint.continuousOn_Iic_primitive_Iic (a₀ := B)
    simpa only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] using
      hc.mono (show Icc (-B) B ⊆ Iic B from fun _ h => h.2)
  have hqin : q.toReal ∈ Icc ((ν (Iic (-B))).toReal) ((ν (Iic B)).toReal) := by
    rw [hcut, hleft, measure_empty, ENNReal.toReal_zero, hcut, hright]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hEfin hq⟩
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (by linarith : -B ≤ B) hcont hqin
  refine ⟨t, ht, ?_⟩
  change (ν (Iic t)).toReal = q.toReal at heq
  rw [hcut] at heq
  have hh := congrArg ENNReal.ofReal heq
  rwa [ENNReal.ofReal_toReal (measure_ne_top_of_subset inter_subset_left hEfin),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top hEfin hq)] at hh

/-- Some point of a finite positive-mass set has at least one quarter of the
mass on either side in a bounded nonatomic coordinate. -/
theorem exists_two_sided_mass_point {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {E : Set X} (hEm : MeasurableSet E) (hEfin : μ E ≠ ∞) (hE0 : μ E ≠ 0)
    (f : X → ℝ) (hf : Measurable f) (hlevel : ∀ t, μ (f ⁻¹' {t}) = 0)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ p ∈ E, |f p| < B) :
    ∃ p ∈ E,
      (μ E).toReal / 4 ≤ (μ (E ∩ {q | f q ≤ f p})).toReal ∧
      (μ E).toReal / 4 ≤ (μ (E ∩ {q | f p ≤ f q})).toReal := by
  let m := (μ E).toReal
  have hm : 0 < m := ENNReal.toReal_pos hE0 hEfin
  obtain ⟨s, _, hs⟩ := exists_coordinate_cut μ hEm hEfin f hf hlevel hB hbound
    ((ENNReal.ofReal_le_iff_le_toReal hEfin).mpr (show m/4 ≤ (μ E).toReal by change m/4 ≤ m; linarith))
  obtain ⟨t, _, ht⟩ := exists_coordinate_cut μ hEm hEfin f hf hlevel hB hbound
    ((ENNReal.ofReal_le_iff_le_toReal hEfin).mpr (show 3*m/4 ≤ (μ E).toReal by change 3*m/4 ≤ m; linarith))
  let Es := E ∩ {p | f p ≤ s}
  let Et := E ∩ {p | f p ≤ t}
  have hsreal : (μ Es).toReal = m/4 := by
    change (μ (E ∩ {p | f p ≤ s})).toReal = _
    rw [hs, ENNReal.toReal_ofReal (by positivity)]
  have htreal : (μ Et).toReal = 3*m/4 := by
    change (μ (E ∩ {p | f p ≤ t})).toReal = _
    rw [ht, ENNReal.toReal_ofReal (by positivity)]
  have hne : (Et \ Es).Nonempty := by
    by_contra hnot
    have hsub : Et ⊆ Es := sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hnot)
    have hh := ENNReal.toReal_mono (measure_ne_top_of_subset inter_subset_left hEfin)
      (measure_mono hsub)
    rw [hsreal, htreal] at hh
    linarith
  obtain ⟨p, hpt, hps⟩ := hne
  have hpE : p ∈ E := hpt.1
  have hspf : s < f p := lt_of_not_ge (fun hle => hps ⟨hpE, hle⟩)
  have hftp : f p ≤ t := hpt.2
  refine ⟨p, hpE, ?_, ?_⟩
  · have hsub : Es ⊆ E ∩ {q | f q ≤ f p} := fun q hq => ⟨hq.1, hq.2.trans hspf.le⟩
    have hh := ENNReal.toReal_mono (measure_ne_top_of_subset inter_subset_left hEfin)
      (measure_mono hsub)
    rw [hsreal] at hh
    exact hh
  · have hEtm : MeasurableSet Et := hEm.inter (measurableSet_le hf measurable_const)
    have hEtE : Et ⊆ E := inter_subset_left
    have hdiff : (μ (E \ Et)).toReal = m - 3*m/4 := by
      rw [measure_sdiff hEtE hEtm.nullMeasurableSet
        (measure_ne_top_of_subset hEtE hEfin), ENNReal.toReal_sub_of_le (measure_mono hEtE) hEfin,
        htreal]
    have hsub : E \ Et ⊆ E ∩ {q | f p ≤ f q} := by
      intro q hq
      refine ⟨hq.1, hftp.trans (le_of_lt ?_)⟩
      exact lt_of_not_ge (fun hle => hq.2 ⟨hq.1, hle⟩)
    have hh := ENNReal.toReal_mono (measure_ne_top_of_subset inter_subset_left hEfin)
      (measure_mono hsub)
    rw [hdiff] at hh
    dsimp [m] at hh ⊢
    linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
