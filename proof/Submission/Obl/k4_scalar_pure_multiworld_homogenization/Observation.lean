import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Source
import Submission.Lib.K4MarginalAveraging.CountedTable
import Submission.Obl.k4_native_base_flattening.AveragingBridge

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction Submission.Lib.K4MarginalAveraging

def joinSwap (q : (Fin 4 → ℝ) × (Fin 2 → ℝ)) : Fin 6 → ℝ := join (q.2, q.1)

theorem measurePreserving_joinSwap :
    MeasurePreserving joinSwap
      ((volume : Measure (Fin 4 → ℝ)).prod (volume : Measure (Fin 2 → ℝ)))
      (volume : Measure (Fin 6 → ℝ)) :=
  measurePreserving_join.comp (Measure.measurePreserving_swap)

theorem map_withDensity_comp_preserving {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : MeasurePreserving f μ ν) {g : β → ENNReal} (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = ν.withDensity g := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ hf.measurable]
  calc
    _ = ∫⁻ a, (g ∘ f) a * (φ ∘ f) a ∂μ :=
      lintegral_withDensity_eq_lintegral_mul _ (hg.comp hf.measurable) (hφ.comp hf.measurable)
    _ = ∫⁻ b, g b * φ b ∂ν := hf.lintegral_comp (hg.mul hφ)
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hg hφ).symm

def chartObservation (a : ℝ) (z : Fin 6 → ℝ) : Observation :=
  (![z 0, z 1], ⌊z 3 / a⌋)

theorem measurable_chartObservation (a : ℝ) : Measurable (chartObservation a) := by
  unfold chartObservation
  fun_prop

theorem chartObservation_joinSwap (a : ℝ) (q : (Fin 4 → ℝ) × (Fin 2 → ℝ)) :
    chartObservation a (joinSwap q) = (q.2, ⌊q.1 1 / a⌋) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem observe_eq_chartObservation (N r : ℝ) :
    observe N r = chartObservation (N ^ (-r)) ∘ chartPoint := rfl

def fibreLabel (a : ℝ) (p : (Fin 4 → ℝ) × (Fin 2 → ℝ)) : ℤ := ⌊p.1 1 / a⌋

theorem measurable_fibreLabel (a : ℝ) : Measurable (fibreLabel a) := by
  unfold fibreLabel
  fun_prop

def marginal (a : ℝ) (f : (Fin 6 → ℝ) → ℝ) : Observation → ENNReal :=
  countedMarginal volume (fun v b => ENNReal.ofReal (f (join (b, v)))) (fibreLabel a)

def realMarginal (a : ℝ) (f : (Fin 6 → ℝ) → ℝ) : Observation → ℝ :=
  realCountedMarginal volume (fun v b => f (join (b, v))) (fibreLabel a)

theorem measurable_marginal (a : ℝ) {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (marginal a f) :=
  countedMarginal_measurable volume (fun v b => ENNReal.ofReal (f (join (b, v))))
    (ENNReal.measurable_ofReal.comp (hf.comp measurePreserving_joinSwap.measurable))
    _ (measurable_fibreLabel a)

theorem measurable_realMarginal (a : ℝ) {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (realMarginal a f) :=
  realCountedMarginal_measurable volume (fun v b => f (join (b, v)))
    (hf.comp measurePreserving_joinSwap.measurable)
    _ (measurable_fibreLabel a)

theorem map_chartObservation_withDensity (a : ℝ) {f : (Fin 6 → ℝ) → ℝ}
    (hf : Measurable f) :
    (volume.withDensity (fun z => ENNReal.ofReal (f z))).map (chartObservation a) =
      reference.withDensity (marginal a f) := by
  rw [← map_withDensity_comp_preserving (g := fun z => ENNReal.ofReal (f z))
    measurePreserving_joinSwap
    (ENNReal.measurable_ofReal.comp hf)]
  rw [Measure.map_map (measurable_chartObservation a) measurePreserving_joinSwap.measurable]
  have hobs : chartObservation a ∘ joinSwap =
      fun q : (Fin 4 → ℝ) × (Fin 2 → ℝ) => (q.2, fibreLabel a q) :=
    funext (chartObservation_joinSwap a)
  rw [hobs]
  exact map_counted_withDensity volume volume (fun v b => ENNReal.ofReal (f (join (b, v))))
    (ENNReal.measurable_ofReal.comp (hf.comp measurePreserving_joinSwap.measurable))
    _ (measurable_fibreLabel a)

theorem integrable_fibre_of_cube {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f)
    {R M : ℝ} (hs : supportedInCube f R) (hb : ∀ z, |f z| ≤ M) (b : Fin 2 → ℝ) :
    Integrable (fun v : Fin 4 → ℝ => f (join (b, v))) := by
  let S : Set (Fin 4 → ℝ) := Icc (fun _ => -R) (fun _ => R)
  have hS : MeasurableSet S := measurableSet_Icc
  let : IsFiniteMeasure ((volume : Measure (Fin 4 → ℝ)).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  have hm : Measurable (fun v : Fin 4 → ℝ => f (join (b, v))) :=
    hf.comp (measurePreserving_join.measurable.comp (measurable_const.prodMk measurable_id))
  have hi : IntegrableOn (fun v : Fin 4 → ℝ => f (join (b, v))) S :=
    Integrable.of_bound hm.stronglyMeasurable.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hb (join (b, v)))
  have heq : S.indicator (fun v : Fin 4 → ℝ => f (join (b, v))) =
      fun v => f (join (b, v)) := by
    funext v
    by_cases hv : v ∈ S
    · exact indicator_of_mem hv _
    · rw [indicator_of_notMem hv]
      have hbad : ∃ j : Fin 4, R < |v j| := by
        have hn : ¬ ∀ j, |v j| ≤ R := by
          intro hh
          apply hv
          exact ⟨(fun j => (abs_le.mp (hh j)).1), (fun j => (abs_le.mp (hh j)).2)⟩
        simpa only [not_forall, not_le] using hn
      obtain ⟨j, hj⟩ := hbad
      have hz : f (join (b, v)) = 0 := by
        fin_cases j
        · exact hs _ 2 hj
        · exact hs _ 3 hj
        · exact hs _ 4 hj
        · exact hs _ 5 hj
      exact hz.symm
  rw [← heq]
  exact hi.integrable_indicator hS

theorem realMarginal_nonneg (a : ℝ) {f : (Fin 6 → ℝ) → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : Observation) : 0 ≤ realMarginal a f z := by
  classical
  unfold realMarginal realCountedMarginal
  apply integral_nonneg
  intro v
  dsimp
  split_ifs
  · exact hf _
  · exact le_rfl

theorem ofReal_realMarginal (a : ℝ) {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f)
    (hf₀ : ∀ z, 0 ≤ f z) {R M : ℝ}
    (hs : supportedInCube f R) (hb : ∀ z, |f z| ≤ M) (z : Observation) :
    ENNReal.ofReal (realMarginal a f z) = marginal a f z :=
  ofReal_realCountedMarginal_of_integrable volume _ _ (measurable_fibreLabel a)
    (integrable_fibre_of_cube hf hs hb) (fun v b => hf₀ _) z

/-- Integrating out the four transverse coordinates contracts the source error. -/
theorem marginal_discrepancy_le (a : ℝ) {f g : (Fin 6 → ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z) {R S M K : ℝ}
    (hsf : supportedInCube f R) (hsg : supportedInCube g S)
    (hbf : ∀ z, |f z| ≤ M) (hbg : ∀ z, |g z| ≤ K) :
    (∫⁻ z, Submission.Obl.k4_native_base_flattening.ediff (marginal a f z) (marginal a g z)
      ∂reference) ≤ densityL1Distance volume f g := by
  calc
    _ = ∫⁻ z, ENNReal.ofReal |realMarginal a f z - realMarginal a g z| ∂reference := by
      apply lintegral_congr
      intro z
      rw [← ofReal_realMarginal a hf hf₀ hsf hbf z,
        ← ofReal_realMarginal a hg hg₀ hsg hbg z]
      exact Submission.Obl.k4_native_base_flattening.ediff_ofReal _ _
        (realMarginal_nonneg a hf₀ z) (realMarginal_nonneg a hg₀ z)
    _ ≤ ∫⁻ q : (Fin 4 → ℝ) × (Fin 2 → ℝ),
        ENNReal.ofReal |f (joinSwap q) - g (joinSwap q)| ∂volume.prod volume :=
      counted_marginal_lintegral_abs_sub_le volume volume
        (fun v b => f (join (b, v))) (fun v b => g (join (b, v)))
        (hf.comp measurePreserving_joinSwap.measurable)
        (hg.comp measurePreserving_joinSwap.measurable)
        (integrable_fibre_of_cube hf hsf hbf) (integrable_fibre_of_cube hg hsg hbg)
        _ (measurable_fibreLabel a)
    _ = densityL1Distance volume f g :=
      measurePreserving_joinSwap.lintegral_comp (ENNReal.measurable_ofReal.comp (hf.sub hg).abs)

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
