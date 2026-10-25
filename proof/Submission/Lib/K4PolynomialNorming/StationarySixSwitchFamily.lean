/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.StationarySixSwitchExperiment
import Submission.Lib.K4PolynomialNorming.ConditionedBasisDeterminants
import Submission.Lib.K4PolynomialNorming.SixSwitchCertificates
import Submission.Lib.K4PolynomialNorming.EndpointSourceSelection

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

section

attribute [local irreducible] causalRetentionWeights

/-- Original state bounds and actual six retention decisions certify the
explicit observed endpoint data under that same weighted path law. -/
theorem stationary_six_basis_switch_certificates_ae {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (P : Measure (L × ℝ)) [IsProbabilityMeasure P]
    (S : Kernel (L × ℝ) (L × ℝ)) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (control : L → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r)
    (Long : Set (L × ℝ)) (hLong : MeasurableSet Long)
    (w₀ : L × ℝ → ENNReal) (hw₀ : Measurable w₀)
    (Good : Set (L × ℝ)) (hwGood : ∀ z, w₀ z ≠ 0 → z ∈ Good)
    (a h U : ℝ) (hh : 0 < h)
    (ht : ∀ᵐ z ∂P, z.2 ∈ Icc a (a+h))
    (hv : ∀ᵐ z ∂P, ∀ j, |v (control z.1) j| ≤ U) :
    ∀ᵐ x ∂(kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
      causalRetentionWeights w₀
        (basisPencilRetention (fun z => control z.1) v r Long) 6
          (Preorder.frestrictLe 6 x)),
      sixSwitchCoordinates control a h x ∈ sixSwitchCertificates Good v (r^3) U := by
  let w : (ℕ → L × ℝ) → ENNReal := fun x => causalRetentionWeights w₀
    (basisPencilRetention (fun z => control z.1) v r Long) 6 (Preorder.frestrictLe 6 x)
  have hd := six_basis_path_determinants_ae (kernelPathMeasure P (fun _ => S))
    (fun z => control z.1) (hcontrol.comp measurable_fst) v r hr Long hLong w₀ hw₀
  have htbox := sixSwitchCoordinates_unit_box_ae P (fun _ => S) (fun _ => hS)
    w control a h hh ht
  have hentries := directionBlockMatrix_sixSwitchCoordinates_abs_le_ae P (fun _ => S)
    (fun _ => hS) w control v a h U hv
  filter_upwards [hd,htbox,hentries] with x hx hb he
  refine ⟨hwGood (x 0) hx.1,?_,he,hb⟩
  intro block
  rw [directionBlockMatrix_sixSwitchCoordinates]
  exact hx.2.2 block

/-- Original conditional breadth, original observation ceilings and actual
endpoint support supply a substantial certified signed-parameter family.
The reference keeps its original start and control masses. -/
theorem stationary_substantial_six_basis_switch_family {L C : Type*}
    [MeasurableSpace L] [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    (P : Measure (L × ℝ)) [IsProbabilityMeasure P]
    (S : Kernel (L × ℝ) (L × ℝ)) [IsMarkovKernel S] (hS : S ∘ₘ P = P)
    (control : L → C) (hcontrol : Measurable control)
    (v : C → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r)
    (Long Good : Set (L × ℝ)) (hLong : MeasurableSet Long) (hGood : MeasurableSet Good)
    (w₀ : L × ℝ → ENNReal) (hw₀ : Measurable w₀) (hw₀1 : ∀ z, w₀ z ≤ 1)
    (hwGood : ∀ z, w₀ z ≠ 0 → z ∈ Good)
    (μ : Measure (L × ℝ)) [SFinite μ] (π : Measure C) [SigmaFinite π]
    (K p b : ENNReal) (a h U : ℝ) (hh : 0 < h)
    (hzero : P.withDensity w₀ ≤ μ)
    (hcap : ∀ᵐ z ∂P, ((S z).restrict Long).map
      (fun y => (control y.1,(y.2-a)/h)) ≤ K • π.prod (volume : Measure ℝ))
    (hbroad : ∀ᵐ z ∂P, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ W < 3 →
        (S z).map (fun y => control y.1) {c | Metric.infDist (v c) (W : Set _) < r} ≤ p)
    (ht : ∀ᵐ z ∂P, z.2 ∈ Icc a (a+h))
    (hv : ∀ᵐ z ∂P, ∀ j, |v (control z.1) j| ≤ U)
    (F : Set (((L × ℝ) × (Fin 6 → C)) × ((Fin 5 → ℝ) × ℝ)))
    (hF : MeasurableSet F)
    (htarget : ∀ᵐ x ∂(kernelPathMeasure P (fun _ => S)).withDensity (fun x =>
      causalRetentionWeights w₀
        (basisPencilRetention (fun z => control z.1) v r Long) 6
          (Preorder.frestrictLe 6 x)), sixSwitchCoordinates control a h x ∈ F)
    (hpositive : K ^ 6 * (μ.prod (Measure.pi (fun _ : Fin 6 => π))) univ * b +
      6 * (P Longᶜ+p) < (P.withDensity w₀) univ) :
    ∃ row, ∃ A : Set (Fin 6 → ℝ), MeasurableSet A ∧ b < volume A ∧
      ∀ δ ∈ A, (row,splitHeadCoordinates 5 δ) ∈
        sixSwitchCertificates Good v (r^3) U ∩ F := by
  let α := basisPencilRetention (fun z : L × ℝ => control z.1) v r Long
  let w : (ℕ → L × ℝ) → ENNReal := fun x =>
    causalRetentionWeights w₀ α 6 (Preorder.frestrictLe 6 x)
  let θ := (kernelPathMeasure P (fun _ => S)).withDensity w
  have hbudget : (P.withDensity w₀) univ ≤ θ univ + 6*(P Longᶜ+p) :=
    stationary_six_basis_path_mass P S hS (fun z => control z.1)
      (hcontrol.comp measurable_fst) v r Long hLong w₀ hw₀ hw₀1 p hbroad
  have hdom : θ.map (sixSwitchCoordinates control a h) ≤
      K ^ 6 • ((μ.prod (Measure.pi (fun _ : Fin 6 => π))).prod volume) :=
    stationary_six_basis_switch_coordinate_law P S hS control hcontrol v r Long hLong
      w₀ hw₀ hw₀1 μ π K a h hzero hcap
  have hcert := stationary_six_basis_switch_certificates_ae P S hS control hcontrol v r hr.le
    Long hLong w₀ hw₀ Good hwGood a h U hh ht hv
  have hsupport : ∀ᵐ x ∂θ, sixSwitchCoordinates control a h x ∈
      sixSwitchCertificates Good v (r^3) U ∩ F := by
    filter_upwards [hcert,htarget] with x hx hf
    exact ⟨hx,hf⟩
  exact retained_observation_substantial_six_parameter_family θ
    (sixSwitchCoordinates control a h) (sixSwitchCoordinates_measurable control hcontrol a h)
    (μ.prod (Measure.pi (fun _ : Fin 6 => π))) (K^6) b
    ((P.withDensity w₀) univ) (6*(P Longᶜ+p)) hdom hbudget
    (sixSwitchCertificates Good v (r^3) U ∩ F)
    ((sixSwitchCertificates_measurable Good hGood v (r^3) U).inter hF)
    hsupport hpositive

end

end Submission.Lib.K4PolynomialNorming
