import Mathlib

namespace Submission.Obl.k4_affine_cube_directional_poincare

open MeasureTheory

/-- The basis-coordinate map with the prescribed scalar factor. -/
noncomputable def scaledBasisEquiv {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (η : ℝ) (hη : η ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).trans
    (b.equivFun.symm.toContinuousLinearEquiv.trans
      (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) η hη).toContinuousLinearEquiv)

lemma scaledBasisEquiv_apply {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (η : ℝ) (hη : η ≠ 0) (t : Fin n → ℝ) :
    scaledBasisEquiv b η hη (WithLp.toLp 2 t) = η • ∑ i, t i • b i := by
  change η • b.equivFun.symm t = _
  rw [b.equivFun_symm_apply]

lemma scaledBasisEquiv_single {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (η : ℝ) (hη : η ≠ 0) (i : Fin n) :
    scaledBasisEquiv b η hη (WithLp.toLp 2 (Pi.single i 1)) = η • b i := by
  rw [scaledBasisEquiv_apply]
  simp [Pi.single_apply, ite_smul]

/-- Specialize an affine coordinate-cube estimate to a scaled arbitrary basis. -/
theorem directional_poincare_of_affine_estimate {n : ℕ}
    (hbound : ∀ (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (a : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 1 f →
      let Q := (fun t : Fin n → ℝ => a + L (WithLp.toLp 2 t)) ''
        Set.Icc (0 : Fin n → ℝ) 1
      (∫ x in Q, |f x|) - |∫ x in Q, f x| ≤
        ∑ i : Fin n, ∫ x in Q,
          ‖fderiv ℝ f x (L (WithLp.toLp 2 (Pi.single i 1)))‖)
    (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (η : ℝ) (hη : 0 < η) (a : EuclideanSpace ℝ (Fin n))
    (Q : Set (EuclideanSpace ℝ (Fin n)))
    (hQ : Q = (fun t : Fin n → ℝ => a + η • (∑ i, t i • b i)) ''
      Set.Icc (0 : Fin n → ℝ) 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x in Q, |f x|) - |∫ x in Q, f x| ≤
      η * ∑ i : Fin n, ∫ x in Q, ‖fderiv ℝ f x (b i)‖ := by
  have h := hbound (scaledBasisEquiv b η hη.ne') a f hf
  have hs (i : Fin n) : (∑ j : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) j • b j) = b i := by
    simp [Pi.single_apply, ite_smul]
  simp only [scaledBasisEquiv_apply, hs, ← hQ] at h
  have heq (i : Fin n) :
      (∫ x in Q, ‖fderiv ℝ f x (η • b i)‖) =
        η * ∫ x in Q, ‖fderiv ℝ f x (b i)‖ := by
    simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    exact integral_const_mul _ _
  simpa only [heq, Finset.mul_sum] using h

end Submission.Obl.k4_affine_cube_directional_poincare
