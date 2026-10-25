import Submission.Obl.k4_eligibility_sign_description.Descriptions
import ChallengeDeps
set_option linter.unusedVariables false

/-!
# `Submission.k4_eligibility_sign_description`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_eligibility_sign_description`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_eligibility_sign_description/`
belong to this obligation.
-/

theorem Submission.k4_eligibility_sign_description : ∃ m d : ℕ, ∀ (P : MvPolynomial (Fin 4) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (t₀ q a K R : ℝ), P.totalDegree ≤ 2 → Matrix.det D ≠ 0 → 0 < q → 0 < a → 1 ≤ K → 1 ≤ R → ∃ (p : Fin m → MvPolynomial (Fin 3 ⊕ Fin 3) ℝ) (B : Set (Fin m → SignType)), (∀ i, (p i).totalDegree ≤ d) ∧ ∀ s y : EuclideanSpace ℝ (Fin 3), (fun i => SignType.sign (MvPolynomial.eval (Sum.elim (fun k : Fin 3 => s k) (fun k : Fin 3 => y k)) (p i))) ∈ B ↔ ‖s‖ ≤ R ∧ ‖y‖ ≤ R ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ‖Matrix.toEuclideanLin (D⁻¹) (WithLp.toLp 2 (fun i : Fin 2 => (y + t • s) i.castSucc - c i - t * u i))‖ ≤ K ∧ |MvPolynomial.eval ![t, (y + t • s) 0, (y + t • s) 1, (y + t • s) 2] P| ≤ K * a) ∧ ∃ t ∈ Set.Icc t₀ (t₀ + q), K⁻¹ ≤ |MvPolynomial.eval ![t, (y + t • s) 0, (y + t • s) 1, (y + t • s) 2] (MvPolynomial.pderiv (3 : Fin 4) P)| := by
  refine ⟨32, 4, ?_⟩
  intro P D c u t₀ q a K R hP hD hq ha hK hR
  have hlr : t₀ ≤ t₀ + q := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hs := Submission.Obl.k4_eligibility_sign_description.SignRep.slope_norm R hR0
  have hy := Submission.Obl.k4_eligibility_sign_description.SignRep.intercept_norm R hR0
  have hn := Submission.Obl.k4_eligibility_sign_description.SignRep.transverse_norm
    D⁻¹ c u K t₀ (t₀ + q) hK0 hlr
  have hp := Submission.Obl.k4_eligibility_sign_description.SignRep.trace_abs
    P hP (K * a) t₀ (t₀ + q) hlr
  have hd := Submission.Obl.k4_eligibility_sign_description.SignRep.derivative_large
    P hP K⁻¹ t₀ (t₀ + q) hlr
  obtain ⟨p, B, hdeg, hB⟩ := hs.and (hy.and ((hn.and hp).and hd))
  refine ⟨p, B, hdeg, ?_⟩
  intro s y
  simpa only [Submission.Obl.k4_eligibility_sign_description.coords, forall_and] using hB (s, y)
