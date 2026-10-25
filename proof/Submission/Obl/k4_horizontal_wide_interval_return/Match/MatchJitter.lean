/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchJitter.lean (namespace renamed into o250's). -/
import Mathlib

/-!
# Jittering the real coordinate of a pair law

`jitter P w` moves the real coordinate of `P` by an independent uniform amount in
`[0, w]`. It keeps the mass of every set described by the index coordinate, and
interval ceilings at resolution `w` become density ceilings for all measurable sets.
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return.MatchJitter

open MeasureTheory

variable {ι : Type*} [MeasurableSpace ι]

/-- The shift map `((i, x), y) ↦ (i, x + y)`. -/
def shift (q : (ι × ℝ) × ℝ) : ι × ℝ := (q.1.1, q.1.2 + q.2)

lemma measurable_shift : Measurable (shift (ι := ι)) := by
  unfold shift
  exact Measurable.prodMk (measurable_fst.comp measurable_fst)
    ((measurable_snd.comp measurable_fst).add measurable_snd)

/-- Jitter the real coordinate uniformly over `[0, w]`. -/
noncomputable def jitter (P : Measure (ι × ℝ)) (w : ℝ) : Measure (ι × ℝ) :=
  ENNReal.ofReal w⁻¹ • (P.prod (volume.restrict (Set.Icc (0:ℝ) w))).map shift

/-- Jittering keeps the mass of index-described sets. -/
lemma jitter_index (P : Measure (ι × ℝ)) [SFinite P] {w : ℝ} (hw : 0 < w) {S : Set ι}
    (hS : MeasurableSet S) :
    jitter P w {p | p.1 ∈ S} = P {p | p.1 ∈ S} := by
  unfold jitter
  have hm : MeasurableSet {p : ι × ℝ | p.1 ∈ S} := measurable_fst hS
  rw [Measure.smul_apply, Measure.map_apply measurable_shift hm]
  have : shift ⁻¹' {p : ι × ℝ | p.1 ∈ S} = {p : ι × ℝ | p.1 ∈ S} ×ˢ (Set.univ : Set ℝ) := by
    ext q; simp [shift]
  rw [this, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    smul_eq_mul, ← mul_assoc, mul_comm (ENNReal.ofReal w⁻¹), mul_assoc,
    ENNReal.ofReal_inv_of_pos hw, ENNReal.inv_mul_cancel (by simpa using hw) ENNReal.ofReal_ne_top,
    mul_one]

/-- The shear `((i,x), y) ↦ ((i,x), x + y)` preserves `P × Lebesgue`. -/
lemma shear_preserving (P : Measure (ι × ℝ)) [SFinite P] :
    MeasurePreserving (fun q : (ι × ℝ) × ℝ => (q.1, q.1.2 + q.2))
      (P.prod volume) (P.prod volume) := by
  have h := MeasurePreserving.skew_product (μa := P) (μc := (volume : Measure ℝ))
    (μd := (volume : Measure ℝ)) (MeasurePreserving.id P) (g := fun p y => p.2 + y)
    (by
      change Measurable (fun q : (ι × ℝ) × ℝ => q.1.2 + q.2)
      exact (measurable_snd.comp measurable_fst).add measurable_snd)
    (Filter.Eventually.of_forall fun p => (measurePreserving_add_left volume p.2).map_eq)
  simpa using h

/-- Interval ceilings at resolution `w` become density ceilings after jittering. -/
lemma jitter_marginal (P : Measure (ι × ℝ)) [SFinite P] {w : ℝ} (hw : 0 < w)
    {S : Set ι} (hS : MeasurableSet S) {C : ENNReal}
    (hP : ∀ x : ℝ, P {p | p.1 ∈ S ∧ p.2 ∈ Set.Icc (x - w) x} ≤ C * ENNReal.ofReal w)
    {E : Set ℝ} (hE : MeasurableSet E) :
    jitter P w {p | p.1 ∈ S ∧ p.2 ∈ E} ≤ C * volume E := by
  unfold jitter
  have hm : MeasurableSet {p : ι × ℝ | p.1 ∈ S ∧ p.2 ∈ E} :=
    (measurable_fst hS).inter (measurable_snd hE)
  rw [Measure.smul_apply, Measure.map_apply measurable_shift hm, smul_eq_mul]
  -- move the restriction to a set of the product
  have hprod : P.prod (volume.restrict (Set.Icc (0:ℝ) w)) =
      (P.prod volume).restrict ((Set.univ : Set (ι × ℝ)) ×ˢ Set.Icc (0:ℝ) w) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hA : MeasurableSet (shift ⁻¹' {p : ι × ℝ | p.1 ∈ S ∧ p.2 ∈ E}) := measurable_shift hm
  rw [hprod, Measure.restrict_apply hA]
  -- the shear image
  set B : Set ((ι × ℝ) × ℝ) :=
    {q | q.1.1 ∈ S ∧ q.2 ∈ E ∧ q.2 - q.1.2 ∈ Set.Icc (0:ℝ) w} with hBdef
  have hB : MeasurableSet B := by
    refine ((measurable_fst.comp measurable_fst) hS).inter
      ((measurable_snd hE).inter ?_)
    exact (measurable_snd.sub (measurable_snd.comp measurable_fst)) measurableSet_Icc
  have hpre : (fun q : (ι × ℝ) × ℝ => (q.1, q.1.2 + q.2)) ⁻¹' B =
      shift ⁻¹' {p : ι × ℝ | p.1 ∈ S ∧ p.2 ∈ E} ∩ (Set.univ ×ˢ Set.Icc (0:ℝ) w) := by
    ext q
    simp only [hBdef, shift, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_prod, Set.mem_univ, true_and, add_sub_cancel_left]
    tauto
  rw [← hpre, (shear_preserving P).measure_preimage hB.nullMeasurableSet,
    Measure.prod_apply_symm hB]
  -- bound the slices
  have hslice : ∀ e : ℝ, P ((fun x => (x, e)) ⁻¹' B) ≤ E.indicator (fun _ => C * ENNReal.ofReal w) e := by
    intro e
    by_cases he : e ∈ E
    · rw [Set.indicator_of_mem he]
      refine le_trans (measure_mono ?_) (hP e)
      intro p hp
      simp only [hBdef, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc] at hp
      obtain ⟨h1, _, h3, h4⟩ := hp
      exact ⟨h1, by constructor <;> linarith⟩
    · rw [Set.indicator_of_notMem he]
      apply le_of_eq
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards with p hp
      simp only [hBdef, Set.mem_preimage, Set.mem_ofPred_eq] at hp
      exact he hp.2.1
  calc ENNReal.ofReal w⁻¹ * ∫⁻ e, P ((fun x => (x, e)) ⁻¹' B)
      ≤ ENNReal.ofReal w⁻¹ * ∫⁻ e, E.indicator (fun _ => C * ENNReal.ofReal w) e := by
        gcongr with e; exact hslice e
    _ = ENNReal.ofReal w⁻¹ * (C * ENNReal.ofReal w * volume E) := by
        rw [lintegral_indicator_const hE]
    _ = C * volume E := by
        rw [ENNReal.ofReal_inv_of_pos hw]
        have h0 : ENNReal.ofReal w ≠ 0 := by simpa using hw
        calc (ENNReal.ofReal w)⁻¹ * (C * ENNReal.ofReal w * volume E)
            = C * volume E * ((ENNReal.ofReal w)⁻¹ * ENNReal.ofReal w) := by ring
          _ = C * volume E := by
              rw [ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, mul_one]

/-- An almost-everywhere property that survives shifts by `[0, w]` holds after jittering. -/
lemma ae_jitter (P : Measure (ι × ℝ)) [SFinite P] {w : ℝ}
    {R R' : ι → ℝ → Prop} (hR' : MeasurableSet {p : ι × ℝ | R' p.1 p.2})
    (hP : ∀ᵐ p ∂P, R p.1 p.2)
    (hshift : ∀ i x y, R i x → 0 ≤ y → y ≤ w → R' i (x + y)) :
    ∀ᵐ p ∂(jitter P w), R' p.1 p.2 := by
  unfold jitter
  rw [ae_iff, Measure.smul_apply, smul_eq_mul]
  have hc : MeasurableSet {p : ι × ℝ | ¬ R' p.1 p.2} := hR'.compl
  rw [Measure.map_apply measurable_shift hc]
  have h1 : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0:ℝ) w))), R q.1.1 q.1.2 :=
    (Measure.quasiMeasurePreserving_fst).ae hP
  have h2 : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0:ℝ) w))), q.2 ∈ Set.Icc (0:ℝ) w :=
    (Measure.quasiMeasurePreserving_snd).ae (ae_restrict_mem measurableSet_Icc)
  have h3 : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0:ℝ) w))), R' q.1.1 (q.1.2 + q.2) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact hshift _ _ _ hq1 hq2.1 hq2.2
  rw [ae_iff] at h3
  have : shift ⁻¹' {p : ι × ℝ | ¬ R' p.1 p.2} = {q | ¬ R' q.1.1 (q.1.2 + q.2)} := by
    ext q; simp [shift]
  rw [this, h3, mul_zero]

end Submission.Obl.k4_horizontal_wide_interval_return.MatchJitter
