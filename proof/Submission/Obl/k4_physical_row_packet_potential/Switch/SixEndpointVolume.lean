-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/SixEndpointVolume.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Endpoint-cell volume for six signed legs in three base
variables: away from the zero set of the selected endpoint minor, the
switch parameters whose endpoints fall in height windows over base cells
have volume at most (base volume) times (height width) / (minor floor).
This is the six-leg, two-basis analogue of the scalar
`four_parameter_endpoint_volume_le` of `Submission.Lib.K4ScalarSwitching`.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.SixShear

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial Matrix

theorem det_ne_zero_of_mul_eq_one (A Ai : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1) :
    A.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hA
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- The selected minor equals the base determinant times the kernel derivative. -/
theorem eval_endpointMinor_eq (H : MvPolynomial (Fin 6) ℝ) (A Ai B : Matrix (Fin 3) (Fin 3) ℝ)
    (j : Fin 3) (δ : Fin 6 → ℝ) :
    eval δ (Submission.Lib.K4CubicTests.endpointMinorPolynomial H A Ai B selI selJ j) =
      A.det * eval δ (Submission.Lib.K4CubicTests.endpointKernelPolynomial H Ai B selI selJ j) := by
  rw [Submission.Lib.K4CubicTests.endpointMinorPolynomial, map_mul, eval_C]

/-- Six-parameter endpoint volume. Cells live in the five coordinates left
after removing the selected last-block duration from the sheared
coordinates: the three base-endpoint coordinates come first. -/
theorem six_endpoint_cells_volume_le {ι : Type*}
    (H : MvPolynomial (Fin 6) ℝ) (D : ℕ) (hH : H.totalDegree ≤ D)
    (A Ai B : Matrix (Fin 3) (Fin 3) ℝ) (hA : A * Ai = 1) (j : Fin 3)
    (S : Set (Fin 6 → ℝ)) (F : Finset ι) (E : ι → Set (Fin 5 → ℝ)) (c : ι → ℝ)
    {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hE : ∀ i ∈ F, MeasurableSet (E i))
    (hcover : ∀ δ ∈ S, ∃ i ∈ F,
      Fin.removeNth (α := fun _ => ℝ) (selJ j) (sixShearMatrix A B *ᵥ δ) ∈ E i ∧
        |eval δ H - c i| ≤ ε)
    (hjac : ∀ δ ∈ S, κ ≤
      |eval δ (Submission.Lib.K4CubicTests.endpointMinorPolynomial H A Ai B selI selJ j)|) :
    volume S ≤ (∑ i ∈ F, volume (E i)) *
      ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ) := by
  let L := sixShear A Ai B hA
  have hdetL : LinearMap.det (L : (Fin 6 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)) = A.det := sixShear_det A Ai B hA
  have hdetA : A.det ≠ 0 := det_ne_zero_of_mul_eq_one A Ai hA
  have hinv (z : Fin 6 → ℝ) : sixShearInvMatrix Ai B *ᵥ (L z) = z :=
    sixShearInv_mulVec_shear A Ai B hA z
  have hrec (z : Fin 6 → ℝ) :
      Fin.insertNth (α := fun _ => ℝ) (selJ j) (L z (selJ j))
        (Fin.removeNth (α := fun _ => ℝ) (selJ j) (L z)) = L z :=
    Fin.insertNth_self_removeNth _ _
  apply linear_endpoint_cells_volume_le 5 (selJ j) L (by rw [hdetL]; exact hdetA)
    (shearFiber Ai B H j) S F E c D hε hκ hS hE
  · have hm : Measurable (fun z : (Fin 5 → ℝ) × ℝ =>
        eval ((splitAt 5 (selJ j)).symm z) (shearPullback Ai B H)) :=
      (MvPolynomial.continuous_eval _).measurable.comp (splitAt 5 (selJ j)).symm.measurable
    convert hm using 2 with z
    rw [eval_shearFiber, splitAt_symm_apply]
  · intro x
    exact (shearFiber_degree Ai B H j x).trans hH
  · intro z hz
    obtain ⟨i, hi, hbase, hheight⟩ := hcover z hz
    refine ⟨i, hi, ?_, ?_⟩
    · rw [splitAt_apply]
      exact hbase
    · rw [splitAt_apply, eval_shearFiber, hrec, eval_shearPullback, hinv]
      exact hheight
  · intro z hz
    rw [hdetL, splitAt_apply, derivative_shearFiber, hrec, eval_pderiv_shearPullback, hinv,
      ← abs_mul, ← eval_endpointMinor_eq]
    exact hjac z hz

end Submission.Obl.k4_physical_row_packet_potential.Switch
