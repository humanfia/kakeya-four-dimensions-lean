/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ConditionedBasisPaths
import Submission.Lib.K4PolynomialNorming.SixSwitchCoordinates
import Submission.Lib.K4PolynomialNorming.StationaryObservedCaps

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

section

attribute [local irreducible] causalObservedHistory causalRetentionWeights

/-- The actual six basis-building switches have their original product
ceiling in the explicit signed endpoint coordinates. -/
theorem stationary_six_basis_switch_coordinate_law {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (P : Measure (L × ℝ)) [IsProbabilityMeasure P]
    (S : Kernel (L × ℝ) (L × ℝ)) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (control : L → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (Long : Set (L × ℝ)) (hLong : MeasurableSet Long)
    (w₀ : L × ℝ → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ z, w₀ z ≤ 1)
    (μ : Measure (L × ℝ)) [SFinite μ] (π : Measure C) [SigmaFinite π]
    (K : ENNReal) (a h : ℝ)
    (hzero : P.withDensity w₀ ≤ μ)
    (hcap : ∀ᵐ z ∂P, ((S z).restrict Long).map
      (fun y => (control y.1,(y.2-a)/h)) ≤ K • π.prod (volume : Measure ℝ)) :
    (((kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
      causalRetentionWeights w₀
        (basisPencilRetention (fun z => control z.1) v r Long) 6
          (Preorder.frestrictLe 6 x))).map (sixSwitchCoordinates control a h)) ≤
      K ^ 6 • ((μ.prod (Measure.pi (fun _ : Fin 6 => π))).prod
        (volume : Measure ((Fin 5 → ℝ) × ℝ))) := by
  let α := basisPencilRetention (fun z : L × ℝ => control z.1) v r Long
  have hα : ∀ n, Measurable (Function.uncurry (α n)) :=
    basisPencilRetention_measurable _ (hcontrol.comp measurable_fst) v r Long hLong
  have hstep := stationary_retained_history_observation_cap P S hS w₀ hw₀1 α hα Long hLong
    (basisPencilRetention_le_long _ v r Long)
    (fun z => (control z.1,(z.2-a)/h)) (by fun_prop)
    (π.prod (volume : Measure ℝ)) K hcap
  have hz : (P.withDensity w₀).map (id : L × ℝ → L × ℝ) ≤ μ := by simpa using hzero
  have hd := retained_trajectory_six_control_endpoint_law P (fullHistoryMarkovKernel (fun _ => S))
    w₀ hw₀ hw₀1 α hα (basisPencilRetention_le_one _ v r Long)
    (id : L × ℝ → L × ℝ) measurable_id
    (fun _ z => (control z.2.1,(z.2.2-a)/h)) (fun _ => by fun_prop)
    μ π K hz (fun n _ => hstep n)
    (fun z : (L × ℝ) × (Fin 6 → C) => (z.1.2-a)/h) (by fun_prop)
  have he : sixSwitchCoordinates control a h =
      fun x : ℕ → L × ℝ => signedDurationEndpointCoordinates
        (fun z : (L × ℝ) × (Fin 6 → C) => (z.1.2-a)/h)
          (separateObservedCoordinates 6 (causalObservedHistory (id : L × ℝ → L × ℝ)
            (fun _ z => (control z.2.1,(z.2.2-a)/h)) 6 (Preorder.frestrictLe 6 x))) := by
    funext x
    exact sixSwitchCoordinates_eq_observed control a h x
  rw [he]
  exact hd

end

end Submission.Lib.K4PolynomialNorming
