-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_grains_nonsingular_slices.ShearFubini.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Defs

/-!
# Shear Fubini

The map `(u, y, z) ↦ ofTwist f u y z` is a measure-preserving bijection (a shear in the first
coordinate), so the volume of a measurable set is the iterated integral of the lengths of its
grain fibres.
-/

namespace WangZahlLot.Obl.wz_grains_nonsingular_slices

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_separated_cover_refinement
open scoped ENNReal

/-- The shear `(u, y) ↦ (u - c * y, y)` preserves Lebesgue measure on `ℝ × ℝ`. -/
private lemma sf_shear_mp (c : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ => (q.1 - c * q.2, q.2)) volume volume := by
  have h1 : MeasurePreserving (fun p : ℝ × ℝ => (id p.1, (fun y u => u - c * y) p.1 p.2))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id volume)
      (by fun_prop)
      (Filter.Eventually.of_forall fun y => (measurePreserving_sub_right volume (c * y)).map_eq)
  exact (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).comp (h1.comp Measure.measurePreserving_swap)

/-- The standard identification `(z, (a, y)) ↦ (a, y, z)` preserves volume. -/
private lemma sf_std_mp :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => (WithLp.toLp 2 ![p.2.1, p.2.2, p.1] : Space))
      volume volume := by
  have e1 : MeasurePreserving (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ)).symm)
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℝ))
  have e2 := MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)
  have e3 := (PiLp.volume_preserving_toLp (Fin 3)).comp (e2.comp e1)
  convert e3 using 1
  funext p
  ext i
  fin_cases i <;> rfl

/-- The map `(z, (u, y)) ↦ ofTwist f u y z` preserves volume. -/
private lemma sf_ofTwist_mp {f : ℝ → ℝ} (hf : Continuous f) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ => ofTwist f p.2.1 p.2.2 p.1) volume volume := by
  have hsh : MeasurePreserving
      (fun p : ℝ × ℝ × ℝ => (id p.1, (fun z (q : ℝ × ℝ) => (q.1 - f z * q.2, q.2)) p.1 p.2))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id (volume : Measure ℝ))
      (by fun_prop) (Filter.Eventually.of_forall fun z => (sf_shear_mp (f z)).map_eq)
  exact sf_std_mp.comp hsh

theorem measurable_grainFib_volume {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space}
    (hA : MeasurableSet A) :
    Measurable (fun t : ℝ × ℝ => volume (grainFib f A t.1 t.2)) := by
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ => ofTwist f p.1.1 p.2 p.1.2) :=
    (continuous_ofTwist hf).comp
      (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))
  have hS : MeasurableSet {p : (ℝ × ℝ) × ℝ | ofTwist f p.1.1 p.2 p.1.2 ∈ A} :=
    hc.measurable hA
  exact measurable_measure_prodMk_left hS

theorem volume_eq_lintegral_grainFib {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space}
    (hA : MeasurableSet A) :
    volume A = ∫⁻ z, ∫⁻ u, volume (grainFib f A u z) := by
  have hΦ := sf_ofTwist_mp hf
  have hS : MeasurableSet ((fun p : ℝ × ℝ × ℝ => ofTwist f p.2.1 p.2.2 p.1) ⁻¹' A) :=
    hΦ.measurable hA
  rw [← hΦ.measure_preimage hA.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hS]
  refine lintegral_congr fun z => ?_
  have hS' : MeasurableSet
      (Prod.mk z ⁻¹' ((fun p : ℝ × ℝ × ℝ => ofTwist f p.2.1 p.2.2 p.1) ⁻¹' A)) :=
    measurable_prodMk_left hS
  rw [Measure.volume_eq_prod, Measure.prod_apply hS']
  rfl

/-- Measurability of the set of points of `E` lying on grains with short fibres. -/
theorem sparse_measurableSet {f : ℝ → ℝ} (hf : Continuous f) {E : Set Space}
    (hE : MeasurableSet E) (lam : ℝ) :
    MeasurableSet {q | q ∈ E ∧ volume (grainFib f E (twist f q) (q 2)) < ENNReal.ofReal lam} := by
  have hg : Measurable (fun q : Space => volume (grainFib f E (twist f q) (q 2))) :=
    (measurable_grainFib_volume hf hE).comp
      ((continuous_twist hf).measurable.prodMk
        (by fun_prop : Continuous fun q : Space => q 2).measurable)
  exact hE.inter (measurableSet_lt hg measurable_const)

/-- The points of `E` on grains with fibres shorter than `lam` have small volume. -/
theorem sparse_volume_le {f : ℝ → ℝ} (hf : Continuous f) {E : Set Space}
    (hE : MeasurableSet E) (hEb : E ⊆ ball 0 1) {s lam : ℝ} (hs0 : 0 ≤ s) (hlam : 0 ≤ lam)
    (hs : ∀ z ∈ Icc (-1 : ℝ) 1, volume (PS f E z) ≤ ENNReal.ofReal s) :
    volume {q | q ∈ E ∧ volume (grainFib f E (twist f q) (q 2)) < ENNReal.ofReal lam} ≤
      ENNReal.ofReal (2 * lam * s) := by
  set Sp := {q | q ∈ E ∧ volume (grainFib f E (twist f q) (q 2)) < ENNReal.ofReal lam}
    with hSp_def
  have hSp : MeasurableSet Sp := sparse_measurableSet hf hE lam
  have hSpE : Sp ⊆ E := fun q hq => hq.1
  -- the fibre of the sparse part over a grain is controlled by the slice `PS f E z`
  have hfib : ∀ u z, volume (grainFib f Sp u z) ≤
      (PS f E z).indicator (fun _ => ENNReal.ofReal lam) u := by
    intro u z
    by_cases hu : u ∈ PS f E z
    · rw [indicator_of_mem hu]
      by_cases hlt : volume (grainFib f E u z) < ENNReal.ofReal lam
      · exact (measure_mono (grainFib_mono hSpE u z)).trans hlt.le
      · have h0 : grainFib f Sp u z = ∅ := by
          ext y
          simp only [mem_empty_iff_false, iff_false]
          intro hy
          apply hlt
          have h := hy.2
          simpa only [twist_ofTwist, ofTwist_two] using h
        rw [h0, measure_empty]
        exact zero_le
    · rw [indicator_of_notMem hu]
      have hne : ¬ (grainFib f E u z).Nonempty := fun h => hu (mem_PS_iff.mpr h)
      rw [not_nonempty_iff_eq_empty] at hne
      have h0 : grainFib f Sp u z = ∅ := subset_empty_iff.mp (hne ▸ grainFib_mono hSpE u z)
      rw [h0, measure_empty]
  -- no fibre outside the heights `[-1, 1]`
  have hout : ∀ u z, z ∉ Icc (-1 : ℝ) 1 → grainFib f Sp u z = ∅ := by
    intro u z hz
    ext y
    simp only [mem_empty_iff_false, iff_false]
    intro hy
    apply hz
    have h1 := mem_ball_zero_iff.mp (hEb (hSpE hy))
    have h2 : |z| ≤ ‖ofTwist f u y z‖ := PiLp.norm_apply_le (ofTwist f u y z) 2
    exact abs_le.mp (h2.trans h1.le)
  have hz : ∀ z, ∫⁻ u, volume (grainFib f Sp u z) ≤
      (Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (lam * s)) z := by
    intro z
    by_cases hz : z ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hz]
      calc ∫⁻ u, volume (grainFib f Sp u z)
          ≤ ∫⁻ u, (PS f E z).indicator (fun _ => ENNReal.ofReal lam) u :=
            lintegral_mono (fun u => hfib u z)
        _ ≤ ENNReal.ofReal lam * volume (PS f E z) := lintegral_indicator_const_le _ _
        _ ≤ ENNReal.ofReal lam * ENNReal.ofReal s := by gcongr; exact hs z hz
        _ = ENNReal.ofReal (lam * s) := (ENNReal.ofReal_mul hlam).symm
    · rw [indicator_of_notMem hz]
      simp [hout _ z hz]
  calc volume Sp = ∫⁻ z, ∫⁻ u, volume (grainFib f Sp u z) :=
        volume_eq_lintegral_grainFib hf hSp
    _ ≤ ∫⁻ z, (Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (lam * s)) z :=
        lintegral_mono hz
    _ = ENNReal.ofReal (lam * s) * volume (Icc (-1 : ℝ) 1) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (2 * lam * s) := by
      rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end WangZahlLot.Obl.wz_grains_nonsingular_slices
