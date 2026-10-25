/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PathSupport.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathReference

/-! The common path law is supported on every actual selected chart piece.
The incidence masks remain separate from the full assigned trajectory priors. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def selectedPreimage {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    Set (Fin (W q k) × State) :=
  {z | (w.incidenceEquiv hp k z.1).symm z.2 ∈ w.selected k z.1}

theorem measurableSet_selectedPreimage {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    MeasurableSet (selectedPreimage w hp k) := by
  have heq : selectedPreimage w hp k =
      ⋃ i, ({i} ×ˢ ((w.incidenceEquiv hp k i).symm ⁻¹' w.selected k i)) := by
    ext z
    simp [selectedPreimage]
  rw [heq]
  exact MeasurableSet.iUnion fun i => (measurableSet_singleton i).prod
    (((w.charts k).2.2.2.1 i).2.preimage (w.incidenceEquiv hp k i).symm.measurable)

theorem selectedPreimage_ae {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p) (k : ℕ) :
    ∀ᵐ z ∂worldMixture q k, z ∈ selectedPreimage w hp k := by
  rw [worldMixture, ← Measure.sum_fintype]
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (Measure.smul_absolutelyContinuous).ae_le
  apply (ae_map_iff
    (show Measurable (fun z : State => (i, z)) from
      measurable_const.prodMk measurable_id).aemeasurable
        (measurableSet_selectedPreimage w hp k)).mpr
  change ∀ᵐ z ∂mu q k i, (w.incidenceEquiv hp k i).symm z ∈ w.selected k i
  rw [w.incidence_eq hp k i]
  apply (Measure.smul_absolutelyContinuous).ae_le
  apply (ae_map_iff (w.incidenceEquiv hp k i).measurable.aemeasurable
    (((w.charts k).2.2.2.1 i).2.preimage
      (w.incidenceEquiv hp k i).symm.measurable)).mpr
  filter_upwards [ae_restrict_mem ((w.charts k).2.2.2.1 i).2] with z hz
  simpa using hz

namespace RefinementChain

theorem map_absolutelyContinuous {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    (worldMixture z k).map (chain.pullback k) ≪ worldMixture p (chain.sample k) := by
  exact (Measure.absolutelyContinuous_smul
    (ENNReal.ofReal_pos.mpr (chain.budget_pos k)).ne').trans
      (Measure.absolutelyContinuous_of_le (chain.originalLaw_le k))

theorem pullback_ae {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    {P : Fin (W p (chain.sample k)) × State → Prop}
    (hP : ∀ᵐ a ∂worldMixture p (chain.sample k), P a) :
    ∀ᵐ a ∂worldMixture z k, P (chain.pullback k a) :=
  ae_of_ae_map (chain.measurable_pullback k).aemeasurable
    ((chain.map_absolutelyContinuous k).ae_le hP)

def pathSet {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    Set (Fin (W z k) × State) :=
  match chain with
  | .nil _ => univ
  | .cons w hp tail =>
    tail.pathSet k ∩ tail.pullback k ⁻¹' selectedPreimage w hp (tail.sample k)

theorem measurableSet_pathSet {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    MeasurableSet (chain.pathSet k) := by
  induction chain with
  | nil => exact MeasurableSet.univ
  | cons w hp tail ih =>
    exact ih.inter ((measurableSet_selectedPreimage w hp _).preimage
      (tail.measurable_pullback k))

/-- Every layer's original selection holds on the same full-measure core
of the final mixture, including after arbitrary later dominated selection. -/
theorem pathSet_ae {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    ∀ᵐ a ∂worldMixture z k, a ∈ chain.pathSet k := by
  induction chain with
  | nil => exact Eventually.of_forall fun _ => mem_univ _
  | cons w hp tail ih =>
    exact ih.and (tail.pullback_ae k (selectedPreimage_ae w hp (tail.sample k)))

theorem pathSet_ae_normalized {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    ∀ᵐ a ∂normalizedWorldMixture z k, a ∈ chain.pathSet k :=
  (Measure.smul_absolutelyContinuous).ae_le (chain.pathSet_ae k)

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
