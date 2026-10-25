/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/Jitter3.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/Jitter3.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Quad3

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Jittering the base point of a pair law in three dimensions

Adapted from the one-dimensional `MatchJitter` of LOT tree g-oai-074, o227
(`k4_horizontal_three_projection_wide_return`), session x0788, branch x0788, commit 6357db85
(`MatchJitter.lean`): the same shear/Fubini argument with the interval `[0, w]` replaced by the
cube `[0, w]³` in `EuclideanSpace ℝ (Fin 3)`.

`jitter3 P w` moves the base point of `P` by an independent uniform vector of the cube
`[0, w]³`.  It keeps the mass of every set described by the index coordinate, and cube ceilings
at resolution `w` become density ceilings for all measurable sets.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open MeasureTheory

variable {ι : Type*} [MeasurableSpace ι]

/-- The cube `[0, w]³`. -/
def cube (w : ℝ) : Set E3 := {u | ∀ k, u k ∈ Set.Icc (0 : ℝ) w}

theorem measurableSet_cube (w : ℝ) : MeasurableSet (cube w) := by
  have : cube w = ⋂ k : Fin 3, (fun u : E3 => u k) ⁻¹' Set.Icc (0 : ℝ) w := by
    ext u; simp [cube]
  rw [this]
  exact MeasurableSet.iInter fun k =>
    (measurable_pi_apply k |>.comp (PiLp.continuous_ofLp 2 _).measurable) measurableSet_Icc

theorem volume_cube {w : ℝ} (hw : 0 ≤ w) : volume (cube w) = ENNReal.ofReal (w ^ 3) := by
  have hpre : cube w = WithLp.ofLp ⁻¹' Set.Icc (0 : Fin 3 → ℝ) (fun _ => w) := by
    ext u; simp [cube, Set.mem_Icc, Pi.le_def, forall_and]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hw]

/-- The shift map `((i, x), u) ↦ (i, x + u)`. -/
def shift3 (q : (ι × E3) × E3) : ι × E3 := (q.1.1, q.1.2 + q.2)

theorem measurable_shift3 : Measurable (shift3 (ι := ι)) := by
  unfold shift3
  exact Measurable.prodMk (measurable_fst.comp measurable_fst)
    ((measurable_snd.comp measurable_fst).add measurable_snd)

/-- Jitter the base point uniformly over `[0, w]³`. -/
noncomputable def jitter3 (P : Measure (ι × E3)) (w : ℝ) : Measure (ι × E3) :=
  (ENNReal.ofReal (w ^ 3))⁻¹ • (P.prod (volume.restrict (cube w))).map shift3

/-- Jittering keeps the mass of index-described sets. -/
theorem jitter3_index (P : Measure (ι × E3)) [SFinite P] {w : ℝ} (hw : 0 < w) {S : Set ι}
    (hS : MeasurableSet S) :
    jitter3 P w {p | p.1 ∈ S} = P {p | p.1 ∈ S} := by
  unfold jitter3
  have hm : MeasurableSet {p : ι × E3 | p.1 ∈ S} := measurable_fst hS
  rw [Measure.smul_apply, Measure.map_apply measurable_shift3 hm]
  have : shift3 ⁻¹' {p : ι × E3 | p.1 ∈ S} = {p : ι × E3 | p.1 ∈ S} ×ˢ (Set.univ : Set E3) := by
    ext q; simp [shift3]
  have hw3 : ENNReal.ofReal (w ^ 3) ≠ 0 := by simpa using pow_pos hw 3
  rw [this, Measure.prod_prod, Measure.restrict_apply_univ, volume_cube hw.le, smul_eq_mul,
    ← mul_assoc, mul_comm (ENNReal.ofReal (w ^ 3))⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel hw3 ENNReal.ofReal_ne_top, mul_one]

/-- The shear `((i,x), u) ↦ ((i,x), x + u)` preserves `P × volume`. -/
theorem shear3_preserving (P : Measure (ι × E3)) [SFinite P] :
    MeasurePreserving (fun q : (ι × E3) × E3 => (q.1, q.1.2 + q.2))
      (P.prod volume) (P.prod volume) := by
  have h := MeasurePreserving.skew_product (μa := P) (μc := (volume : Measure E3))
    (μd := (volume : Measure E3)) (MeasurePreserving.id P) (g := fun p y => p.2 + y)
    (by
      change Measurable (fun q : (ι × E3) × E3 => q.1.2 + q.2)
      exact (measurable_snd.comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall fun p => (measurePreserving_add_left volume p.2).map_eq)
  simpa using h

/-- Cube ceilings at resolution `w` become density ceilings after jittering. -/
theorem jitter3_marginal (P : Measure (ι × E3)) [SFinite P] {w : ℝ} (hw : 0 < w)
    {S : Set ι} (hS : MeasurableSet S) {C : ENNReal}
    (hP : ∀ y : E3, P {p | p.1 ∈ S ∧ y - p.2 ∈ cube w} ≤ C * ENNReal.ofReal (w ^ 3))
    {U : Set E3} (hU : MeasurableSet U) :
    jitter3 P w {p | p.1 ∈ S ∧ p.2 ∈ U} ≤ C * volume U := by
  unfold jitter3
  have hm : MeasurableSet {p : ι × E3 | p.1 ∈ S ∧ p.2 ∈ U} :=
    (measurable_fst hS).inter (measurable_snd hU)
  rw [Measure.smul_apply, Measure.map_apply measurable_shift3 hm, smul_eq_mul]
  have hprod : P.prod (volume.restrict (cube w)) =
      (P.prod volume).restrict ((Set.univ : Set (ι × E3)) ×ˢ cube w) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hA : MeasurableSet (shift3 ⁻¹' {p : ι × E3 | p.1 ∈ S ∧ p.2 ∈ U}) := measurable_shift3 hm
  rw [hprod, Measure.restrict_apply hA]
  set Bs : Set ((ι × E3) × E3) :=
    {q | q.1.1 ∈ S ∧ q.2 ∈ U ∧ q.2 - q.1.2 ∈ cube w} with hBdef
  have hB : MeasurableSet Bs := by
    refine ((measurable_fst.comp measurable_fst) hS).inter ((measurable_snd hU).inter ?_)
    exact (measurable_snd.sub (measurable_snd.comp measurable_fst)) (measurableSet_cube w)
  have hpre : (fun q : (ι × E3) × E3 => (q.1, q.1.2 + q.2)) ⁻¹' Bs =
      shift3 ⁻¹' {p : ι × E3 | p.1 ∈ S ∧ p.2 ∈ U} ∩ (Set.univ ×ˢ cube w) := by
    ext q
    simp only [hBdef, shift3, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_prod, Set.mem_univ, true_and, add_sub_cancel_left]
    tauto
  rw [← hpre, (shear3_preserving P).measure_preimage hB.nullMeasurableSet,
    Measure.prod_apply_symm hB]
  have hslice : ∀ e : E3, P ((fun x => (x, e)) ⁻¹' Bs) ≤
      U.indicator (fun _ => C * ENNReal.ofReal (w ^ 3)) e := by
    intro e
    by_cases he : e ∈ U
    · rw [Set.indicator_of_mem he]
      refine le_trans (measure_mono ?_) (hP e)
      intro p hp
      simp only [hBdef, Set.mem_preimage, Set.mem_ofPred_eq] at hp
      exact ⟨hp.1, hp.2.2⟩
    · rw [Set.indicator_of_notMem he]
      apply le_of_eq
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards with p hp
      simp only [hBdef, Set.mem_preimage, Set.mem_ofPred_eq] at hp
      exact he hp.2.1
  have hw3 : ENNReal.ofReal (w ^ 3) ≠ 0 := by simpa using pow_pos hw 3
  calc (ENNReal.ofReal (w ^ 3))⁻¹ * ∫⁻ e, P ((fun x => (x, e)) ⁻¹' Bs)
      ≤ (ENNReal.ofReal (w ^ 3))⁻¹ * ∫⁻ e, U.indicator (fun _ => C * ENNReal.ofReal (w ^ 3)) e := by
        gcongr with e; exact hslice e
    _ = (ENNReal.ofReal (w ^ 3))⁻¹ * (C * ENNReal.ofReal (w ^ 3) * volume U) := by
        rw [lintegral_indicator_const hU]
    _ = C * volume U := by
        calc (ENNReal.ofReal (w ^ 3))⁻¹ * (C * ENNReal.ofReal (w ^ 3) * volume U)
            = C * volume U * ((ENNReal.ofReal (w ^ 3))⁻¹ * ENNReal.ofReal (w ^ 3)) := by ring
          _ = C * volume U := by
              rw [ENNReal.inv_mul_cancel hw3 ENNReal.ofReal_ne_top, mul_one]

/-- An almost-everywhere property that survives shifts by `[0, w]³` holds after jittering. -/
theorem ae_jitter3 (P : Measure (ι × E3)) [SFinite P] {w : ℝ}
    {R R' : ι → E3 → Prop} (hR' : MeasurableSet {p : ι × E3 | R' p.1 p.2})
    (hP : ∀ᵐ p ∂P, R p.1 p.2)
    (hshift : ∀ i x u, R i x → u ∈ cube w → R' i (x + u)) :
    ∀ᵐ p ∂(jitter3 P w), R' p.1 p.2 := by
  unfold jitter3
  rw [ae_iff, Measure.smul_apply, smul_eq_mul]
  have hc : MeasurableSet {p : ι × E3 | ¬ R' p.1 p.2} := hR'.compl
  rw [Measure.map_apply measurable_shift3 hc]
  have h1 : ∀ᵐ q ∂(P.prod (volume.restrict (cube w))), R q.1.1 q.1.2 :=
    (Measure.quasiMeasurePreserving_fst).ae hP
  have h2 : ∀ᵐ q ∂(P.prod (volume.restrict (cube w))), q.2 ∈ cube w :=
    (Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem (measurableSet_cube w))
  have h3 : ∀ᵐ q ∂(P.prod (volume.restrict (cube w))), R' q.1.1 (q.1.2 + q.2) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact hshift _ _ _ hq1 hq2
  rw [ae_iff] at h3
  have : shift3 ⁻¹' {p : ι × E3 | ¬ R' p.1 p.2} = {q | ¬ R' q.1.1 (q.1.2 + q.2)} := by
    ext q; simp [shift3]
  rw [this, h3, mul_zero]

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
