/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file CoefficientWorldChoice.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalWorldChoice
import Submission.Obl.k4_scalar_graph_residual_discovery.ParameterRefinement
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldDensity

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_crop_angular_finite_tail

namespace Zoom

noncomputable section

/-- Choose the coefficient world only AFTER globally charged cuts. Its
reference is the entire original coefficient-bin prior, independent of
the selected labels and of the number or sizes of coefficient worlds. -/
theorem exists_dense_coefficient_world
    (θ : Measure ScalarLine) [IsFiniteMeasure θ] (μ : Measure ScalarIncidence)
    (ρ : ℝ) (E : Set ScalarIncidence) (hE : MeasurableSet E)
    (hθ : θ univ ≤ 1) {U : ℝ≥0∞} (hdom : μ.restrict E ≤ U • θ.prod volume)
    {δ : ℝ} (hδ : 0 < δ) (hmass : ENNReal.ofReal δ ≤ μ E) :
    ∃ q : Fin 5 → ℤ, θ {l | cell ρ l.2 = q} ≠ 0 ∧
      IsProbabilityMeasure (prior θ ρ q) ∧
      ENNReal.ofReal (δ / 2) * θ {l | cell ρ l.2 = q} ≤
        μ (E ∩ {p | cell ρ p.1.2 = q}) := by
  let code (p : ScalarIncidence) := cell ρ p.1.2
  let block (q : Fin 5 → ℤ) : Set ScalarLine := {l | cell ρ l.2 = q}
  have hcode : Measurable code := measurable_cell ρ (measurable_snd.comp measurable_fst)
  have hprior : (∑' q : Fin 5 → ℤ, (1 : ℝ≥0∞) * θ (block q)) ≤ 1 := by
    have hh := measure_eq_tsum_label θ (measurable_cell ρ measurable_snd) MeasurableSet.univ
    have hsum : (∑' q : Fin 5 → ℤ, θ (block q)) = θ univ := by
      simpa only [univ_inter, block, Set.preimage, mem_singleton_iff] using hh.symm
    simpa only [one_mul, hsum] using hθ
  have htotal : ENNReal.ofReal δ ≤
      ∑' q : Fin 5 → ℤ, (1 : ℝ≥0∞) * μ (E ∩ code ⁻¹' {q}) := by
    simpa only [one_mul, ← measure_eq_tsum_label μ hcode hE] using hmass
  have hzero (q : Fin 5 → ℤ) (hq : θ (block q) = 0) : μ (E ∩ code ⁻¹' {q}) = 0 := by
    apply le_zero_iff.mp
    calc
      _ = (μ.restrict E) (code ⁻¹' {q}) := by
        rw [Measure.restrict_apply (hcode (measurableSet_singleton q)), inter_comm]
      _ ≤ (U • θ.prod volume) (code ⁻¹' {q}) := hdom _
      _ = 0 := by
        have heq : code ⁻¹' {q} = block q ×ˢ (univ : Set ℝ) := by ext p; simp [code, block]
        rw [heq, Measure.smul_apply, Measure.prod_prod, hq, zero_mul]
        exact smul_zero U
  obtain ⟨q, _, hq, hfound⟩ := exists_original_weighted_dense_component
    (fun _ : Fin 5 → ℤ => 1) (fun q => θ (block q))
    (fun q => μ (E ∩ code ⁻¹' {q})) hδ hprior htotal hzero
  refine ⟨q, hq, prior_probability θ ρ q hq, ?_⟩
  simpa only [code, Set.preimage, mem_singleton_iff] using hfound

/-- The selected full coefficient prior supports a genuinely dense
labelled product world, with only the original density ceiling lost. -/
theorem exists_dense_coefficient_product_world
    (θ : Measure ScalarLine) [IsFiniteMeasure θ] (μ : Measure ScalarIncidence)
    (ρ : ℝ) (E : Set ScalarIncidence) (hE : MeasurableSet E)
    (hθ : θ univ ≤ 1) {H δ : ℝ} (hH : 0 < H)
    (hdom : μ.restrict E ≤ ENNReal.ofReal H • θ.prod volume)
    (hδ : 0 < δ) (hmass : ENNReal.ofReal δ ≤ μ E) :
    ∃ q : Fin 5 → ℤ, θ {l | cell ρ l.2 = q} ≠ 0 ∧
      IsProbabilityMeasure (prior θ ρ q) ∧
      ENNReal.ofReal (δ / (2 * H)) ≤
        ((prior θ ρ q).prod volume) (E ∩ {p | cell ρ p.1.2 = q}) := by
  obtain ⟨q, hq, hprob, hmass⟩ := exists_dense_coefficient_world θ μ ρ E hE hθ hdom hδ hmass
  have hcode : Measurable (fun p : ScalarIncidence => cell ρ p.1.2) :=
    measurable_cell ρ (measurable_snd.comp measurable_fst)
  have hworld : MeasurableSet (E ∩ {p : ScalarIncidence | cell ρ p.1.2 = q}) :=
    hE.inter (hcode (measurableSet_singleton q))
  have hmass' : ENNReal.ofReal (δ / 2) * θ {l | cell ρ l.2 = q} ≤
      (μ.restrict E) (E ∩ {p | cell ρ p.1.2 = q}) := by
    rwa [Measure.restrict_apply hworld, inter_eq_left.mpr inter_subset_left]
  have hh := prior_product_dense θ (μ.restrict E) hH hdom q hq hworld
    (fun _ hp => hp.2) hmass'
  have heq : (δ / 2) / H = δ / (2 * H) := by ring
  exact ⟨q, hq, hprob, by simpa only [heq] using hh⟩

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
