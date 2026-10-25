import Submission.Obl.k4_scalar_capped_heavy_potential.Core.SwitchSupport
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Geometry

/-!
# Continuity of the simulated endpoint and the curl of the rescaled field
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

theorem eval_legField_eq (A B : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ)
    (j : Fin 4) (s : ℝ) :
    eval (Sum.elim δ (fun _ : Unit => s)) (legField A B x v j) =
      eval (fun d => x d + (∑ k : Fin 4, if k.val < j.val then
          ((![1, v k] : Fin 2 → ℝ) d) * δ k else 0) + ((![1, v j] : Fin 2 → ℝ) d) * s) A +
        v j * eval (fun d => x d + (∑ k : Fin 4, if k.val < j.val then
          ((![1, v k] : Fin 2 → ℝ) d) * δ k else 0) + ((![1, v j] : Fin 2 → ℝ) d) * s) B := by
  rw [legField, map_add, map_mul, eval_C, eval_substitution, eval_substitution]
  simp only [eval_legPoint]

theorem continuous_legPointEval (j : Fin 4) :
    Continuous (fun p : ((Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ)) × ℝ =>
      fun d : Fin 2 => p.1.1 d + (∑ k : Fin 4, if k.val < j.val then
        ((![1, p.1.2.1 k] : Fin 2 → ℝ) d) * p.1.2.2 k else 0) +
          ((![1, p.1.2.1 j] : Fin 2 → ℝ) d) * p.2) := by
  apply continuous_pi
  intro d
  fin_cases d
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, one_mul]
    apply Continuous.add
    · apply Continuous.add
      · fun_prop
      · apply continuous_finset_sum
        intro k _
        split_ifs <;> fun_prop
    · fun_prop
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply Continuous.add
    · apply Continuous.add
      · fun_prop
      · apply continuous_finset_sum
        intro k _
        split_ifs <;> fun_prop
    · fun_prop

/-- The simulated height is jointly continuous in the start, the controls and
the increments. -/
theorem continuous_brokenHeight_eval (A B : MvPolynomial (Fin 2) ℝ) :
    Continuous (fun z : (Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      eval z.2.2 (brokenHeight A B z.1 z.2.1)) := by
  have heq : (fun z : (Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      eval z.2.2 (brokenHeight A B z.1 z.2.1)) = fun z => ∑ j : Fin 4,
        ∫ s in (0 : ℝ)..z.2.2 j, eval (Sum.elim z.2.2 (fun _ : Unit => s))
          (legField A B z.1 z.2.1 j) := by
    funext z
    exact eval_brokenHeight A B z.1 z.2.1 z.2.2
  rw [heq]
  apply continuous_finset_sum
  intro j _
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · have hfun : Function.uncurry (fun (z : (Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ)) (s : ℝ) =>
        eval (Sum.elim z.2.2 (fun _ : Unit => s)) (legField A B z.1 z.2.1 j)) =
        fun p : ((Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ)) × ℝ =>
          eval (fun d => p.1.1 d + (∑ k : Fin 4, if k.val < j.val then
            ((![1, p.1.2.1 k] : Fin 2 → ℝ) d) * p.1.2.2 k else 0) +
              ((![1, p.1.2.1 j] : Fin 2 → ℝ) d) * p.2) A +
          p.1.2.1 j * eval (fun d => p.1.1 d + (∑ k : Fin 4, if k.val < j.val then
            ((![1, p.1.2.1 k] : Fin 2 → ℝ) d) * p.1.2.2 k else 0) +
              ((![1, p.1.2.1 j] : Fin 2 → ℝ) d) * p.2) B := by
      funext p
      exact eval_legField_eq A B p.1.1 p.1.2.1 p.1.2.2 j p.2
    rw [hfun]
    apply Continuous.add
    · exact (MvPolynomial.continuous_eval A).comp (continuous_legPointEval j)
    · exact (by fun_prop : Continuous fun p : ((Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ)) × ℝ =>
        p.1.2.1 j).mul ((MvPolynomial.continuous_eval B).comp (continuous_legPointEval j))
  · fun_prop

theorem continuous_switchedBaseEndpoint :
    Continuous (fun z : (Fin 2 → ℝ) × (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      switchedBaseEndpoint z.1 z.2.1 z.2.2) := by
  apply continuous_pi
  intro d
  simp only [switchedBaseEndpoint]
  apply Continuous.add
  · fun_prop
  · apply continuous_finset_sum
    intro k _
    fin_cases d
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, one_mul]; fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]; fun_prop

/-! ### The curl of the rescaled field -/

theorem pderiv_scaleField (s : ℝ) (P : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
    pderiv i (scaleField s P) = C s * (aeval (fun k => C s * X k) (pderiv i P) * C s) := by
  rw [scaleField, pderiv_C_mul, partial_aeval, Fin.sum_univ_two]
  fin_cases i <;> simp [pderiv_C_mul, pderiv_X, Pi.single_apply]

theorem eval_pderiv_scaleField (s : ℝ) (P : MvPolynomial (Fin 2) ℝ) (i : Fin 2)
    (z : Fin 2 → ℝ) :
    eval z (pderiv i (scaleField s P)) = s ^ 2 * eval (fun k => s * z k) (pderiv i P) := by
  rw [pderiv_scaleField, map_mul, map_mul, eval_C, eval_substitution]
  simp only [map_mul, eval_C, eval_X]
  ring

theorem abs_coeff_pderiv_le (P : MvPolynomial (Fin 2) ℝ) {D : ℕ} (hP : P.totalDegree ≤ D)
    {H : ℝ} (hH : 0 ≤ H) (hcoeff : ∀ b, |P.coeff b| ≤ H) (i : Fin 2) (m : Fin 2 →₀ ℕ) :
    |(pderiv i P).coeff m| ≤ ((D : ℝ) + 1) * H := by
  rw [coeff_pderiv, abs_mul]
  by_cases h0 : P.coeff (m + Finsupp.single i 1) = 0
  · rw [h0, abs_zero, zero_mul]
    positivity
  · have hmem : m + Finsupp.single i 1 ∈ P.support := mem_support_iff.mpr h0
    have hdeg := (le_totalDegree hmem).trans hP
    have hmi : m i + 1 ≤ D := by
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hdeg
      fin_cases i <;> simp [Finsupp.single_apply] at hdeg ⊢ <;> omega
    have hcast : |((m i : ℝ) + 1)| ≤ (D : ℝ) + 1 := by
      rw [abs_of_nonneg (by positivity)]
      have : ((m i : ℝ) + 1) ≤ (D : ℝ) := by exact_mod_cast hmi
      linarith
    calc
      |P.coeff (m + Finsupp.single i 1)| * |((m i : ℝ) + 1)| ≤ H * ((D : ℝ) + 1) :=
        mul_le_mul (hcoeff _) hcast (abs_nonneg _) hH
      _ = ((D : ℝ) + 1) * H := by ring

/-- Sup bound of the curl of the rescaled field on the unit box. -/
theorem scaleField_curl_eval_le {s : ℝ} (hs : 1 ≤ s) (A B : MvPolynomial (Fin 2) ℝ) {D : ℕ}
    (hA : A.totalDegree ≤ D) (hB : B.totalDegree ≤ D) {H : ℝ} (hH : 0 ≤ H)
    (hAc : ∀ b, |A.coeff b| ≤ H) (hBc : ∀ b, |B.coeff b| ≤ H)
    (z : Fin 2 → ℝ) (hz : z ∈ Icc (-1 : Fin 2 → ℝ) 1) :
    |eval z (pderiv 0 (scaleField s B) - pderiv 1 (scaleField s A))| ≤
      s ^ (D + 2) * (((D + 1) ^ 2 : ℕ) * (2 * (((D : ℝ) + 1) * H))) := by
  rw [map_sub, eval_pderiv_scaleField, eval_pderiv_scaleField, ← mul_sub, ← map_sub,
    abs_mul, abs_of_nonneg (by positivity)]
  set Q := pderiv 0 B - pderiv 1 A
  have hQ : Q.totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    exact max_le ((Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le B 0).trans
        ((Nat.sub_le _ _).trans hB))
      ((Submission.Lib.K4PolynomialPotential.totalDegree_pderiv_le A 1).trans
        ((Nat.sub_le _ _).trans hA))
  have hQc : ∀ b, |Q.coeff b| ≤ 2 * (((D : ℝ) + 1) * H) := by
    intro b
    rw [coeff_sub]
    have h1 := abs_coeff_pderiv_le B hB hH hBc 0 b
    have h2 := abs_coeff_pderiv_le A hA hH hAc 1 b
    calc
      |(pderiv 0 B).coeff b - (pderiv 1 A).coeff b| ≤
          |(pderiv 0 B).coeff b| + |(pderiv 1 A).coeff b| := abs_sub _ _
      _ ≤ 2 * (((D : ℝ) + 1) * H) := by linarith
  have hbox : ∀ i, |s * z i| ≤ s := by
    intro i
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
    have : |z i| ≤ 1 := abs_le.mpr ⟨by simpa using hz.1 i, by simpa using hz.2 i⟩
    nlinarith
  have h1 := eval_le_coefficientMass_on_box Q hQ hs _ hbox
  have h2 := Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass_le_of_coeff_bound
    Q hQ (by positivity) hQc
  calc
    s ^ 2 * |eval (fun k => s * z k) Q| ≤ s ^ 2 * (s ^ D * (((D + 1) ^ 2 : ℕ) *
        (2 * (((D : ℝ) + 1) * H)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = s ^ (D + 2) * (((D + 1) ^ 2 : ℕ) * (2 * (((D : ℝ) + 1) * H))) := by ring

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
