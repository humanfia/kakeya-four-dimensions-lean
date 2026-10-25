-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/PushDensity.lean (session x0254's own proofs), renamed into this namespace.
import Mathlib

/-!
# Densities of labeled observations

If a measure on `B × F` has a density `φ` with respect to `μB ⊗ μF`, then recording the
base point together with two countable labels of the fiber gives a measure with density
`y ↦ ∫⁻_{label cell of y} φ(b, w) dμF(w)` with respect to `μB ⊗ count ⊗ count`.
This is Tonelli's theorem plus the partition of the fiber into label cells.
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MeasureTheory Set
open scoped ENNReal

section Labels

variable {B F J V : Type*} [MeasurableSpace B] [MeasurableSpace F]
  [MeasurableSpace J] [MeasurableSpace V] [Countable J] [Countable V]
  [MeasurableSingletonClass J] [MeasurableSingletonClass V]

/-- The label cell `{w | l₁ w = j ∧ l₂ w = v}`. -/
def labelCell (l₁ : F → J) (l₂ : F → V) (j : J) (v : V) : Set F :=
  {w | l₁ w = j ∧ l₂ w = v}

omit [Countable J] [Countable V] in
theorem measurableSet_labelCell {l₁ : F → J} {l₂ : F → V} (hl₁ : Measurable l₁)
    (hl₂ : Measurable l₂) (j : J) (v : V) : MeasurableSet (labelCell l₁ l₂ j v) :=
  (hl₁ (measurableSet_singleton j)).inter (hl₂ (measurableSet_singleton v))

/-- The density of the labeled law. -/
noncomputable def labelDensity (μF : Measure F) (l₁ : F → J) (l₂ : F → V)
    (φ : B × F → ℝ≥0∞) : (B × J) × V → ℝ≥0∞ :=
  fun y => ∫⁻ w in labelCell l₁ l₂ y.1.2 y.2, φ (y.1.1, w) ∂μF

theorem measurable_labelDensity (μF : Measure F) [SFinite μF] {l₁ : F → J} {l₂ : F → V}
    (hl₁ : Measurable l₁) (hl₂ : Measurable l₂) {φ : B × F → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (labelDensity μF l₁ l₂ φ) := by
  apply measurable_from_prod_countable_left
  intro v
  apply measurable_from_prod_countable_left
  intro j
  have h : Measurable fun q : B × F =>
      (labelCell l₁ l₂ j v).indicator (fun w => φ (q.1, w)) q.2 := by
    have hm : Measurable fun q : B × F => φ (q.1, q.2) := hφ
    exact hm.indicator (measurable_snd (measurableSet_labelCell hl₁ hl₂ j v))
  have h2 := h.lintegral_prod_right' (ν := μF)
  have heq : (fun b : B => labelDensity μF l₁ l₂ φ ((b, j), v)) =
      fun b => ∫⁻ w, (labelCell l₁ l₂ j v).indicator (fun w => φ (b, w)) w ∂μF := by
    funext b
    simp only [labelDensity]
    rw [lintegral_indicator (measurableSet_labelCell hl₁ hl₂ j v)]
  rw [heq]
  exact h2

/-- Integral over the fiber as a sum over the label cells. -/
theorem lintegral_eq_tsum_labelCell (μF : Measure F) {l₁ : F → J} {l₂ : F → V}
    (hl₁ : Measurable l₁) (hl₂ : Measurable l₂) (f : F → ℝ≥0∞) :
    ∫⁻ w, f w ∂μF = ∑' j, ∑' v, ∫⁻ w in labelCell l₁ l₂ j v, f w ∂μF := by
  have hU : (⋃ p : J × V, labelCell l₁ l₂ p.1 p.2) = univ := by
    ext w
    simp only [mem_iUnion, mem_univ, iff_true]
    exact ⟨(l₁ w, l₂ w), rfl, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun p : J × V => labelCell l₁ l₂ p.1 p.2) := by
    intro p q hpq
    refine Set.disjoint_left.mpr ?_
    intro w hp hq
    apply hpq
    exact Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2)
  rw [← setLIntegral_univ, ← hU,
    lintegral_iUnion (s := fun p : J × V => labelCell l₁ l₂ p.1 p.2)
      (fun p => measurableSet_labelCell hl₁ hl₂ p.1 p.2) hdisj]
  exact ENNReal.tsum_prod (f := fun j v => ∫⁻ w in labelCell l₁ l₂ j v, f w ∂μF)

/-- **Labeled pushforward.** -/
theorem map_labels_withDensity (μB : Measure B) (μF : Measure F) [SFinite μB] [SFinite μF]
    {l₁ : F → J} {l₂ : F → V} (hl₁ : Measurable l₁) (hl₂ : Measurable l₂)
    {φ : B × F → ℝ≥0∞} (hφ : Measurable φ) :
    Measure.map (fun q : B × F => ((q.1, l₁ q.2), l₂ q.2)) ((μB.prod μF).withDensity φ) =
      ((μB.prod Measure.count).prod Measure.count).withDensity
        (labelDensity μF l₁ l₂ φ) := by
  have hπ : Measurable (fun q : B × F => ((q.1, l₁ q.2), l₂ q.2)) :=
    (measurable_fst.prodMk (hl₁.comp measurable_snd)).prodMk (hl₂.comp measurable_snd)
  have hh := measurable_labelDensity μF hl₁ hl₂ hφ (B := B)
  ext s hs
  have hind : Measurable (s.indicator (labelDensity μF l₁ l₂ φ)) := hh.indicator hs
  rw [Measure.map_apply hπ hs, withDensity_apply _ (hπ hs), withDensity_apply _ hs,
    ← lintegral_indicator (hπ hs), ← lintegral_indicator hs,
    lintegral_prod _ ((hφ.indicator (hπ hs)).aemeasurable),
    lintegral_prod _ hind.aemeasurable,
    lintegral_prod _ (hind.lintegral_prod_right' (ν := Measure.count)).aemeasurable]
  apply lintegral_congr
  intro b
  rw [lintegral_eq_tsum_labelCell μF hl₁ hl₂]
  simp only [lintegral_count]
  refine tsum_congr (fun j => tsum_congr (fun v => ?_))
  have hcell := measurableSet_labelCell hl₁ hl₂ j v
  by_cases hmem : ((b, j), v) ∈ s
  · rw [indicator_of_mem hmem]
    apply setLIntegral_congr_fun hcell
    intro w hw
    have hw' : ((b, l₁ w), l₂ w) ∈ s := by rw [hw.1, hw.2]; exact hmem
    simp [indicator, hw']
  · rw [indicator_of_notMem hmem]
    rw [setLIntegral_congr_fun hcell (g := fun _ => 0)]
    · simp
    · intro w hw
      have hw' : ((b, l₁ w), l₂ w) ∉ s := by rw [hw.1, hw.2]; exact hmem
      simp [indicator, hw']

end Labels

/-- Transport of a density along a measure-preserving measurable equivalence. -/
theorem map_withDensity_comp_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (f : β → ℝ≥0∞) :
    Measure.map e (μ.withDensity (f ∘ e)) = ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (e.measurable hs), ← lintegral_indicator hs]
  have h := he.lintegral_comp_emb e.measurableEmbedding (s.indicator f)
  rw [← h]
  rfl

end Submission.Obl.k4_native_shear_source_transport
