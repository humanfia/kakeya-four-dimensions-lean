/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.OriginalSupportRelations
import Submission.Lib.K4PolynomialNorming.StationaryKernelPaths

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Original stationary almost-sure state properties hold simultaneously
at all actual times, after any weighting of the original path law. -/
theorem kernelPathMeasure_weighted_ae_states {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (K : ℕ → Kernel X X)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ P = P)
    (w : (ℕ → X) → ENNReal) (R : ℕ → X → Prop)
    (hR : ∀ n, ∀ᵐ z ∂P, R n z) :
    ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w, ∀ n, R n (x n) := by
  apply (withDensity_absolutelyContinuous (kernelPathMeasure P K) w).ae_le
  apply ae_all_iff.mpr
  intro n
  have h := hR n
  rw [← kernelPathMeasure_stationary_marginal P K hK n] at h
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable h

/-- Original conditional transition properties hold simultaneously on
every leg of a weighted path, with the original Markov coupling. -/
theorem kernelPathMeasure_weighted_ae_steps {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (K : ℕ → Kernel X X)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ P = P)
    (w : (ℕ → X) → ENNReal) (R : ℕ → Set (X × X))
    (hR : ∀ n, MeasurableSet (R n))
    (hstep : ∀ n, ∀ᵐ z ∂P, ∀ᵐ y ∂K n z, (z,y) ∈ R n) :
    ∀ᵐ x ∂(kernelPathMeasure P K).withDensity w,
      ∀ n, (x n,x (n+1)) ∈ R n := by
  apply (withDensity_absolutelyContinuous (kernelPathMeasure P K) w).ae_le
  exact ae_all_iff.mpr (fun n => kernelPathMeasure_ae_step P K hK n (R n) (hR n)
    (hstep n))

end Submission.Lib.K4PolynomialNorming
