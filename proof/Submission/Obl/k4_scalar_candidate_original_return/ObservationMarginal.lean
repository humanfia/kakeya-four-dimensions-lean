import Submission.Obl.k4_scalar_candidate_original_return.ObservationFormat
import Submission.Lib.K4MarginalAveraging.MarginalAE
import Submission.Lib.K4MarginalAveraging.CountedAveraging
import Submission.Obl.k4_native_shear_source_transport.PushDensity
import Submission.Lib.K4ModelReduction.AveragingComposition

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4MarginalAveraging Submission.Lib.K4ModelReduction

noncomputable section

abbrev Hidden := Fin 4 → ℝ

def fiberBaseCoordinates : (Fin 6 → ℝ) ≃ᵐ Hidden × Base :=
  scalarSplit.trans MeasurableEquiv.prodComm

lemma measurePreserving_fiberBaseCoordinates :
    MeasurePreserving fiberBaseCoordinates (volume : Measure (Fin 6 → ℝ))
      ((volume : Measure Hidden).prod (volume : Measure Base)) :=
  Measure.measurePreserving_swap.comp measurePreserving_scalarSplit

lemma fiberBaseCoordinates_symm_apply (z : Hidden × Base) :
    fiberBaseCoordinates.symm z = ![z.2 0, z.2 1, z.1 0, z.1 1, z.1 2, z.1 3] :=
  scalarSplit_symm_apply (z.2, z.1)

def fiberSource (f : (Fin 6 → ℝ) → ℝ) (h : Hidden) (b : Base) : ℝ :=
  f (scalarSplit.symm (b, h))

lemma measurable_fiberSource {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (Function.uncurry (fiberSource f)) :=
  hf.comp fiberBaseCoordinates.symm.measurable

lemma integrable_fiberSource {f : (Fin 6 → ℝ) → ℝ} (hf : Integrable f volume) :
    Integrable (Function.uncurry (fiberSource f))
      ((volume : Measure Hidden).prod (volume : Measure Base)) :=
  (measurePreserving_fiberBaseCoordinates.symm fiberBaseCoordinates).integrable_comp_of_integrable hf

def hiddenObservationTag (δ : ℝ) (h : Hidden) : ℤ := ⌊h 1 / δ⌋

lemma measurable_hiddenObservationTag (δ : ℝ) : Measurable (hiddenObservationTag δ) := by
  unfold hiddenObservationTag
  fun_prop

def rawObservation (δ : ℝ) (w : Fin 6 → ℝ) : Base × ℤ :=
  (![w 0, w 1], ⌊w 3 / δ⌋)

lemma measurable_rawObservation (δ : ℝ) : Measurable (rawObservation δ) := by
  unfold rawObservation
  apply Measurable.prodMk _ (by fun_prop)
  apply Measurable.of_eval
  intro i
  fin_cases i <;> fun_prop

/-- A real representative of the exact terminal-observation density. -/
def scalarMarginal (δ : ℝ) (f : (Fin 6 → ℝ) → ℝ) : Base × ℤ → ℝ :=
  realCountedMarginal volume (fiberSource f) (fun z => hiddenObservationTag δ z.1)

lemma scalarMarginal_measurable (δ : ℝ) {f : (Fin 6 → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (scalarMarginal δ f) :=
  realCountedMarginal_measurable volume (fiberSource f) (measurable_fiberSource hf) _
    ((measurable_hiddenObservationTag δ).comp measurable_fst)

lemma scalarMarginal_nonneg (δ : ℝ) {f : (Fin 6 → ℝ) → ℝ} (hf : ∀ w, 0 ≤ f w)
    (z : Base × ℤ) : 0 ≤ scalarMarginal δ f z := by
  classical
  unfold scalarMarginal realCountedMarginal
  apply integral_nonneg
  intro h
  dsimp only
  split
  · exact hf _
  · exact le_rfl

/-- Original terminal observation is the counted marginal of the exact full
scalar source; exceptional divergent fibers do not affect the measure identity. -/
theorem map_rawObservation_withDensity (δ : ℝ) {f : (Fin 6 → ℝ) → ℝ}
    (hf : Measurable f) (hfi : Integrable f volume) (hf0 : ∀ w, 0 ≤ f w) :
    (volume.withDensity (fun w => ENNReal.ofReal (f w))).map (rawObservation δ) =
      ((volume : Measure Base).prod Measure.count).withDensity
        (fun z => ENNReal.ofReal (scalarMarginal δ f z)) := by
  have htransport := k4_native_shear_source_transport.map_withDensity_comp_equiv
    fiberBaseCoordinates.symm (measurePreserving_fiberBaseCoordinates.symm fiberBaseCoordinates)
    (fun w => ENNReal.ofReal (f w))
  rw [← htransport, Measure.map_map (measurable_rawObservation δ)
    fiberBaseCoordinates.symm.measurable]
  have hmap : rawObservation δ ∘ fiberBaseCoordinates.symm =
      fun z : Hidden × Base => (z.2, hiddenObservationTag δ z.1) := by
    funext z
    rw [Function.comp_apply, rawObservation, fiberBaseCoordinates_symm_apply]
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  rw [hmap]
  exact map_counted_withDensity_real_of_integrable_product volume volume (fiberSource f)
    (measurable_fiberSource hf) _ ((measurable_hiddenObservationTag δ).comp measurable_fst)
    (integrable_fiberSource hfi) (fun h b => hf0 _)

/-- Marginalization charges no factor in the number of original hidden bins. -/
theorem scalarMarginal_error (δ : ℝ) {f g : (Fin 6 → ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ z, ENNReal.ofReal |scalarMarginal δ f z - scalarMarginal δ g z|
      ∂(volume : Measure Base).prod Measure.count) ≤ densityL1Distance volume f g := by
  apply (counted_marginal_lintegral_abs_sub_le_of_measurable volume volume
    (fiberSource f) (fiberSource g) (measurable_fiberSource hf) (measurable_fiberSource hg)
    _ ((measurable_hiddenObservationTag δ).comp measurable_fst)).trans_eq
  exact (measurePreserving_fiberBaseCoordinates.symm fiberBaseCoordinates).lintegral_comp_emb
    fiberBaseCoordinates.symm.measurableEmbedding (fun w => ENNReal.ofReal |f w - g w|)

/-- Averaging the two base coordinates yields a posterior rule that is
constant on each actual base cell and each original hidden tag. -/
theorem scalarMarginal_same_cell (δ ρ : ℝ) {f : (Fin 6 → ℝ) → ℝ}
    (hcell : ∀ w w', (∀ i ∉ ([0, 1] : List (Fin 6)), w i = w' i) →
      (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊w i / ρ⌋ = ⌊w' i / ρ⌋) → f w = f w')
    (b b' : Base) (hfloor : ∀ i, ⌊b i / ρ⌋ = ⌊b' i / ρ⌋) (a : ℤ) :
    scalarMarginal δ f (b, a) = scalarMarginal δ f (b', a) := by
  apply realCountedMarginal_same_cell volume (fiberSource f) (hiddenObservationTag δ) ρ
    (fun h x x' hx => ?_) b b' hfloor a
  apply hcell
  · intro i hi
    fin_cases i <;> simp_all [scalarSplit_symm_apply]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · simpa [scalarSplit_symm_apply] using hx 0
    · simpa [scalarSplit_symm_apply] using hx 1

end

end Submission.Obl.k4_scalar_candidate_original_return
