import Submission.Obl.k4_affine_cube_directional_poincare.Basis
import Submission.Obl.k4_affine_cube_directional_poincare.Transport
import Submission.Obl.k4_affine_cube_directional_poincare.Cube
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# Directional L1 oscillation on affine basis cubes

The coordinate-cube inequality is transported through the affine Jacobian.
Scaling the basis directions then gives the dimensional constant `P = 1`.
-/

open MeasureTheory

theorem Submission.k4_affine_cube_directional_poincare : ∀ n : ℕ, 1 ≤ n → ∃ P : ℝ, 0 < P ∧ ∀ (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ), 0 < η → ∀ (a : EuclideanSpace ℝ (Fin n)) (Q : Set (EuclideanSpace ℝ (Fin n))), Q = (fun t : Fin n → ℝ => a + η • (∑ i : Fin n, t i • b i)) '' Set.Icc (0 : Fin n → ℝ) 1 → ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → MeasureTheory.integral (MeasureTheory.volume.restrict Q) (fun x => |f x|) - |MeasureTheory.integral (MeasureTheory.volume.restrict Q) f| ≤ η * P * (∑ i : Fin n, MeasureTheory.integral (MeasureTheory.volume.restrict Q) (fun x : EuclideanSpace ℝ (Fin n) => ‖(fderiv ℝ f x) (b i)‖)) := by
  intro n hn
  refine ⟨1, zero_lt_one, ?_⟩
  intro b η hη a Q hQ f hf
  have hbound : ∀ (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (a : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 1 f →
      let Q := (fun t : Fin n → ℝ => a + L (WithLp.toLp 2 t)) ''
        Set.Icc (0 : Fin n → ℝ) 1
      (∫ x in Q, |f x|) - |∫ x in Q, f x| ≤
        ∑ i : Fin n, ∫ x in Q,
          ‖fderiv ℝ f x (L (WithLp.toLp 2 (Pi.single i 1)))‖ := by
    intro L a f hf
    apply Submission.Obl.k4_affine_cube_directional_poincare.ambient_poincare_of_coordinate_bound
    exact Submission.Obl.k4_affine_cube_directional_poincare.affine_cube_poincare
      ((L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap)
      a f hf
  simpa only [mul_one] using
    Submission.Obl.k4_affine_cube_directional_poincare.directional_poincare_of_affine_estimate
      hbound b η hη a Q hQ f hf
