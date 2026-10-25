/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.ConditionedBasisPaths
import Submission.Lib.K4DeterminantBreadth

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Successive distance floors give the determinant floor for the actual
three direction columns, using the accepted Gram-Schmidt estimate. -/
theorem column_triple_det_ge_of_distances
    (f : Fin 3 → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r)
    (hgood : ∀ j : Fin 3, r ≤ Metric.infDist (f j)
      (Submodule.span ℝ (f '' Set.Iio j) : Set (EuclideanSpace ℝ (Fin 3)))) :
    r ^ 3 ≤ |(Matrix.of (fun a i => f i a)).det| := by
  have hp : r ^ 3 ≤ ∏ i : Fin 3, Metric.infDist (f i)
      (Submodule.span ℝ (f '' Set.Iio i) : Set (EuclideanSpace ℝ (Fin 3))) := by
    calc
      _ = ∏ _i : Fin 3, r := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hr) (fun i _ => hgood i)
  have hd := hp.trans (Submission.Lib.K4DeterminantBreadth.abs_det_ge_prod_infDist 3 f)
  change r ^ 3 ≤ |(Matrix.transpose (Matrix.of (fun a i => f i a))).det| at hd
  simpa only [Matrix.det_transpose] using hd

/-- Six original retained basis-building decisions certify both actual
basis determinants almost everywhere in the same retained path law. -/
theorem six_basis_path_determinants_ae {X C : Type*}
    [MeasurableSpace X] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (Q : Measure (ℕ → X)) (control : X → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) (Long : Set X)
    (hLong : MeasurableSet Long) (w₀ : X → ENNReal) (hw₀ : Measurable w₀) :
    ∀ᵐ x ∂Q.withDensity (fun x =>
        causalRetentionWeights w₀ (basisPencilRetention control v r Long) 6
          (Preorder.frestrictLe 6 x)),
      w₀ (x 0) ≠ 0 ∧ (∀ k < 6, x (k+1) ∈ Long) ∧
        ∀ b : Fin 2, r ^ 3 ≤
          |(Matrix.of (fun a i : Fin 3 => v (control (x (3*b.1+i.1+1))) a)).det| := by
  filter_upwards [six_basis_path_certificates_ae Q control hcontrol v r Long hLong w₀ hw₀]
    with x hx
  refine ⟨hx.1,hx.2.1,fun b => ?_⟩
  exact column_triple_det_ge_of_distances
    (fun i : Fin 3 => v (control (x (3*b.1+i.1+1)))) r hr (hx.2.2 b)

end Submission.Lib.K4PolynomialNorming
