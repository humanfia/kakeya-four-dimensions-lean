/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Submission.Lib.K4ContactAffine.InteriorChart
import Submission.Lib.K4AffineMeshCaps.Transport

/-!+# Original cell ceilings in the interior contact chart

The chart contracts each base direction, so the same old mesh resolves each
new mesh. The exact Jacobian costs only `243 R²` in the cell cap. Any original
incidence condition, including a velocity bin, is retained.
-/

namespace Submission.Lib.K4ContactAffine

open Set MeasureTheory Matrix
open Submission.Lib.K4AffineMeshCaps

noncomputable section

def interiorMatrix (R : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / 3, 0, 0; 0, 1 / R, 0; -1 / 6, 1 / (3 * R), 1 / (3 * R)]

def interiorShift : Fin 3 → ℝ := ![1 / 3, 1 / 2, 7 / 12]

theorem interiorBase_affine (R : ℝ) (z : Fin 3 → ℝ) :
    interiorBase R z = affineBase (interiorMatrix R) interiorShift z := by
  funext i
  fin_cases i <;> simp [interiorBase, affineBase, interiorMatrix, interiorShift,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem det_interiorMatrix (R : ℝ) : (interiorMatrix R).det = 1 / (9 * R ^ 2) := by
  simp [interiorMatrix, Matrix.det_fin_three]
  ring

theorem interiorMatrix_resolves (R : ℝ) (hR : 1 ≤ R) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ i, (∑ j, |interiorMatrix R i j| * δ) ≤ δ := by
  have hR0 : 0 < R := by linarith
  have hinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
  have hinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  intro i
  fin_cases i <;> simp [interiorMatrix, Fin.sum_univ_three, abs_of_pos hR0,
    abs_of_pos (show 0 < 3 * R by positivity), div_eq_mul_inv]
  all_goals nlinarith [mul_le_mul_of_nonneg_right hinv1 hδ]

theorem interior_cap_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {R δ C : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (Z p) = q ∧ condition p} ≤ ENNReal.ofReal (C * δ ^ 3)) :
    ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh δ (interiorBase R (Z p)) = q ∧ condition p} ≤
        ENNReal.ofReal (243 * C * R ^ 2 * δ ^ 3) := by
  have hR0 : 0 < R := by linarith
  have hM : (interiorMatrix R).det ≠ 0 := by rw [det_interiorMatrix]; positivity
  have hdet : |(interiorMatrix R).det|⁻¹ = 9 * R ^ 2 := by
    rw [det_interiorMatrix, abs_of_pos (by positivity)]
    simp
  intro q
  have hh := affine_mesh_cell_cap μ Z condition (interiorMatrix R) interiorShift hM
    hδ hδ hC (interiorMatrix_resolves R hR hδ.le) hcap q
  simp_rw [← interiorBase_affine] at hh
  rw [hdet] at hh
  convert hh using 1; ring

/-- The joint cap keeps the identical original palette-bin factor. The chart
scales the actual velocity and its mesh together. -/
theorem interior_joint_bin_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (b : Ω → Fin 6 → ℝ)
    (π : Measure ℝ) [IsFiniteMeasure π]
    {R δ η C : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) (hη : η ≠ 0) (hC : 0 ≤ C)
    (hcap : ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | baseMesh δ (Z p) = q ∧ ⌊b p 3 / η⌋ = a} ≤
        ENNReal.ofReal (C * δ ^ 3) * π {w | ⌊w / η⌋ = a}) :
    ∀ (q : Fin 3 → ℤ) (a : ℤ),
      μ {p | baseMesh δ (interiorBase R (Z p)) = q ∧
        ⌊interiorCoeff R (b p) 3 / (3 * η / R)⌋ = a} ≤
        ENNReal.ofReal (243 * C * R ^ 2 * δ ^ 3) * π {w | ⌊w / η⌋ = a} := by
  have hR0 : 0 < R := by linarith
  intro q a
  let r := (π {w | ⌊w / η⌋ = a}).toReal
  have hr : ENNReal.ofReal r = π {w | ⌊w / η⌋ = a} :=
    ENNReal.ofReal_toReal (measure_ne_top π _)
  have hCr : 0 ≤ C * r := mul_nonneg hC ENNReal.toReal_nonneg
  have hcap' : ∀ q' : Fin 3 → ℤ,
      μ {p | baseMesh δ (Z p) = q' ∧ ⌊b p 3 / η⌋ = a} ≤
        ENNReal.ofReal ((C * r) * δ ^ 3) := by
    intro q'
    have he : ENNReal.ofReal ((C * r) * δ ^ 3) =
        ENNReal.ofReal (C * δ ^ 3) * π {w | ⌊w / η⌋ = a} := by
      rw [← hr, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C * δ ^ 3)]
      congr 1
      ring
    rw [he]
    exact hcap q' a
  have hh := interior_cap_transfer μ Z (fun p => ⌊b p 3 / η⌋ = a) hR hδ hCr hcap' q
  have he : ENNReal.ofReal (243 * (C * r) * R ^ 2 * δ ^ 3) =
      ENNReal.ofReal (243 * C * R ^ 2 * δ ^ 3) * π {w | ⌊w / η⌋ = a} := by
    rw [← hr, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 243 * C * R ^ 2 * δ ^ 3)]
    congr 1
    ring
  rw [he] at hh
  simpa only [interior_velocity_bin R η hR0.ne' hη] using hh

end

end Submission.Lib.K4ContactAffine
