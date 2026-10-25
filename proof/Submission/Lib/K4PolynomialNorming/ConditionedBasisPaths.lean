/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.HistoryBasisPencils
import Submission.Lib.K4PolynomialNorming.ConditionalRetentionBudget
import Submission.Lib.K4PolynomialNorming.RetainedTrajectorySupport

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Original conditional breadth is valid for the span selected from the
complete actual past, since that span always has dimension less than three. -/
theorem stationary_history_basis_pencil_cap {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (p : ENNReal)
    (hbroad : ∀ᵐ x ∂P, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ W < 3 →
        (S x).map control {c | Metric.infDist (v c) (W : Set _) < r} ≤ p) (n : ℕ) :
    ∀ᵐ h ∂(kernelPathMeasure P (fun _ => S)).map (Preorder.frestrictLe n),
      fullHistoryMarkovKernel (fun _ => S) n h
        {y | (h,control y) ∈ historyBasisPencil control v r n} ≤ p := by
  apply stationary_history_pencil_cap_of_uniform_original P S hS control hcontrol n
    (historyBasisPencil control v r n) (historyBasisPencil_measurable control hcontrol v r n) p
  filter_upwards [hbroad] with x hx
  intro h
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ
    (Set.range (fun i => v (previousBlockControls control n h i)))
  have hW : Module.finrank ℝ W < 3 := historyBasisPencil_span_rank_lt control v n h
  have hh := hx W hW
  change (S x).map control {c | Metric.infDist (v c) (W : Set _) < r} ≤ p
  exact hh

section

attribute [local irreducible] causalRetentionWeights

/-- The six actual basis-building switches retain their original starting
mass after six original short-state and conditional pencil losses. -/
theorem stationary_six_basis_path_mass {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (P : Measure X) [IsProbabilityMeasure P]
    (S : Kernel X X) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (Long : Set X) (hLong : MeasurableSet Long)
    (w₀ : X → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ x, w₀ x ≤ 1) (p : ENNReal)
    (hbroad : ∀ᵐ x ∂P, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ W < 3 →
        (S x).map control {c | Metric.infDist (v c) (W : Set _) < r} ≤ p) :
    (P.withDensity w₀) univ ≤
      ((kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
        causalRetentionWeights w₀ (basisPencilRetention control v r Long) 6
          (Preorder.frestrictLe 6 x))) univ + 6 * (P Longᶜ + p) := by
  have h := stationary_causal_retention_mass_bound_of_conditional_pencils P S hS w₀ hw₀ hw₀1
    (basisPencilRetention control v r Long)
    (basisPencilRetention_measurable control hcontrol v r Long hLong)
    (basisPencilRetention_le_one control v r Long)
    Long hLong control hcontrol (historyBasisPencil control v r)
    (historyBasisPencil_measurable control hcontrol v r) (fun _ => p)
    (stationary_history_basis_pencil_cap P S hS control hcontrol v r p hbroad)
    (basisPencilRetention_defect control v r Long) 6
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] using h

/-- Both actual direction triples and all six long choices are certified
almost everywhere under the original causally retained trajectory law. -/
theorem six_basis_path_certificates_ae {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (Q : Measure (ℕ → X)) (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (Long : Set X)
    (hLong : MeasurableSet Long) (w₀ : X → ENNReal) (hw₀ : Measurable w₀) :
    ∀ᵐ x ∂Q.withDensity (fun x =>
        causalRetentionWeights w₀ (basisPencilRetention control v r Long) 6
          (Preorder.frestrictLe 6 x)),
      w₀ (x 0) ≠ 0 ∧ (∀ k < 6, x (k+1) ∈ Long) ∧
        ∀ b : Fin 2, ∀ j : Fin 3, r ≤ Metric.infDist (v (control (x (3*b.1+j.1+1))))
          (Submodule.span ℝ
            ((fun i : Fin 3 => v (control (x (3*b.1+i.1+1)))) '' Set.Iio j) :
              Set (EuclideanSpace ℝ (Fin 3))) := by
  have h := causal_retained_trajectory_ae_decisions Q w₀ hw₀
    (basisPencilRetention control v r Long)
    (basisPencilRetention_measurable control hcontrol v r Long hLong) 6
  filter_upwards [h] with x hx
  exact ⟨hx.1,six_basis_retention_certificates control v r Long x hx.2⟩

end

end Submission.Lib.K4PolynomialNorming
