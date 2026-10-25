/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/LabelNoise.lean. -/
import Mathlib

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

/-- A countable law whose singleton masses are bounded is dominated by counting
measure with that bound. -/
theorem le_count_of_singletons {B : Type*} [MeasurableSpace B] [Countable B]
    [MeasurableSingletonClass B] (μ : Measure B) (D : ℝ≥0∞)
    (h : ∀ b, μ {b} ≤ D) : μ ≤ D • Measure.count := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [← Measure.sum_smul_dirac μ, Measure.sum_apply _ hA,
    Measure.smul_apply, smul_eq_mul, Measure.count, Measure.sum_apply _ hA,
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun b => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (h b) le_rfl

/-- Appending an arbitrary countable label preserves a singleton cap for an
existing countable label. -/
theorem pair_label_count_bound {P B C : Type*} [MeasurableSpace P]
    [MeasurableSpace B] [MeasurableSpace C] [Countable B] [Countable C]
    [MeasurableSingletonClass B] [MeasurableSingletonClass C]
    (μ : Measure P) (f : P → B) (g : P → C)
    (hf : Measurable f) (hg : Measurable g) (D : ℝ≥0∞)
    (h : ∀ c, μ {p | g p = c} ≤ D) :
    μ.map (fun p => (f p, g p)) ≤ D • (Measure.count : Measure (B × C)) := by
  apply le_count_of_singletons
  intro b
  rw [Measure.map_apply (hf.prodMk hg) (measurableSet_singleton b)]
  exact (measure_mono (fun p hp => (congrArg Prod.snd hp))).trans (h b.2)

/-- An independent real noise with a density ceiling retains that ceiling after
a translation depending on all the other variables. -/
theorem scalar_sheared_product_bound {P : Type*} [MeasurableSpace P]
    (μ : Measure P) [SFinite μ] (β : Measure ℝ) [SFinite β]
    (c : ℝ≥0∞) (hβ : β ≤ c • volume) (shift : P → ℝ) (hshift : Measurable shift) :
    (μ.prod β).map (fun p => (p.1, p.2 + shift p.1)) ≤ c • μ.prod volume := by
  have hT : Measurable (fun p : P × ℝ => (p.1, p.2 + shift p.1)) := by fun_prop
  have hpres : MeasurePreserving (fun p : P × ℝ => (p.1, p.2 + shift p.1))
      (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).skew_product
      (by fun_prop) (Filter.Eventually.of_forall fun p =>
        (measurePreserving_add_right volume (shift p)).map_eq)
  have hmap := Measure.map_mono (Measure.prod_mono (μ := μ) le_rfl hβ) hT
  rw [Measure.prod_smul_right, Measure.map_smul _ hT.aemeasurable, hpres.map_eq] at hmap
  exact hmap

/-- After adjoining independent Lebesgue noise, a bounded countable label law
is bounded by Lebesgue measure times counting measure. -/
theorem label_product_bound {P B : Type*} [MeasurableSpace P] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (μ : Measure P) [SFinite μ] (f : P → B) (hf : Measurable f)
    (D : ℝ≥0∞) (h : μ.map f ≤ D • Measure.count) :
    (μ.prod (volume : Measure ℝ)).map (fun p => (p.2, f p.1)) ≤
      D • (volume : Measure ℝ).prod Measure.count := by
  have heq : (μ.prod (volume : Measure ℝ)).map (fun p => (p.2, f p.1)) =
      (volume : Measure ℝ).prod (μ.map f) := by
    calc
      _ = ((μ.prod volume).map Prod.swap).map (Prod.map id f) := by
        rw [Measure.map_map (measurable_id.prodMap hf) measurable_swap]
        rfl
      _ = ((volume : Measure ℝ).prod μ).map (Prod.map id f) := by rw [Measure.prod_swap]
      _ = _ := by rw [← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id]
  rw [heq]
  simpa only [Measure.prod_smul_right] using
    (Measure.prod_mono (μ := (volume : Measure ℝ)) le_rfl h)


/-- The preceding bound can be used separately at every time, with labels
that depend measurably on time. -/
theorem dependent_label_product_bound {T P B : Type*}
    [MeasurableSpace T] [MeasurableSpace P] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (τ : Measure T) [SFinite τ] (μ : Measure P) [SFinite μ]
    (f : T × P → B) (hf : Measurable f) (D : ℝ≥0∞)
    (h : ∀ t, μ.map (fun p => f (t, p)) ≤ D • Measure.count) :
    ((τ.prod μ).prod (volume : Measure ℝ)).map
        (fun p => (p.1.1, (p.2, f p.1))) ≤
      D • τ.prod ((volume : Measure ℝ).prod Measure.count) := by
  let q : T × (P × ℝ) → T × (ℝ × B) :=
    fun p => (p.1, (p.2.2, f (p.1, p.2.1)))
  have hq : Measurable q := by fun_prop
  have heq : ((τ.prod μ).prod (volume : Measure ℝ)).map
      (fun p => (p.1.1, (p.2, f p.1))) =
        (τ.prod (μ.prod (volume : Measure ℝ))).map q := by
    rw [← Measure.prodAssoc_prod, Measure.map_map hq (by fun_prop)]
    rfl
  rw [heq]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hq hA, Measure.prod_apply (hq hA), Measure.smul_apply,
    smul_eq_mul, Measure.prod_apply hA]
  calc
    _ ≤ ∫⁻ t, D * ((volume : Measure ℝ).prod Measure.count) (Prod.mk t ⁻¹' A) ∂τ := by
      apply lintegral_mono
      intro t
      have ht : Measurable (fun p : P => f (t, p)) := hf.comp measurable_prodMk_left
      have hb := label_product_bound μ (fun p => f (t, p)) ht D (h t)
      have hm : Measurable (fun p : P × ℝ => (p.2, f (t, p.1))) := by fun_prop
      have ha : MeasurableSet (Prod.mk t ⁻¹' A) := hA.preimage measurable_prodMk_left
      simpa only [Measure.map_apply hm ha, Measure.smul_apply, smul_eq_mul, q,
        preimage_preimage, Function.comp_def] using hb (Prod.mk t ⁻¹' A)
    _ = _ := lintegral_const_mul _ (measurable_measure_prodMk_left hA)


/-- Countable observations of a noisy atom have an exact density ceiling,
uniformly in time and in the measurable choice of the discrete label. -/
theorem labelled_noise_bound {T P B : Type*}
    [MeasurableSpace T] [MeasurableSpace P] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (τ : Measure T) [SFinite τ] (μ : Measure P) [SFinite μ]
    (β : Measure ℝ) [SFinite β] (c D : ℝ≥0∞) (hβ : β ≤ c • volume)
    (f : T × P → B) (hf : Measurable f)
    (hlabel : ∀ t, μ.map (fun p => f (t, p)) ≤ D • Measure.count)
    (shift : T × P → ℝ) (hshift : Measurable shift) :
    ((τ.prod μ).prod β).map (fun p => (p.1.1, (p.2 + shift p.1, f p.1))) ≤
      (c * D) • τ.prod ((volume : Measure ℝ).prod Measure.count) := by
  let q : (T × P) × ℝ → T × (ℝ × B) := fun p => (p.1.1, (p.2, f p.1))
  have hq : Measurable q := by fun_prop
  have hshear := scalar_sheared_product_bound (τ.prod μ) β c hβ shift hshift
  have hmono := Measure.map_mono hshear hq
  rw [Measure.map_map hq (by fun_prop), Measure.map_smul _ hq.aemeasurable] at hmono
  exact hmono.trans (by
    simpa only [smul_smul] using smul_le_smul_left c
      (dependent_label_product_bound τ μ f hf D hlabel))

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
