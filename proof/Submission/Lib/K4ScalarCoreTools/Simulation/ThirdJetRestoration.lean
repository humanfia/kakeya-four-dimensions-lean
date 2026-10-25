/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/ThirdJetRestoration.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/ThirdJetRestoration.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientBounds
import Submission.Lib.K4ScalarCoreTools.Simulation.ConservativePotential

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open MvPolynomial Set
open Submission.Lib.K4PolynomialPotential

noncomputable def quadraticTruncation {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ⟨Finsupp.filter (fun e : Fin n →₀ ℕ => e.degree ≤ 2) P.coeff⟩

theorem coeff_quadraticTruncation {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (e : Fin n →₀ ℕ) :
    (quadraticTruncation P).coeff e = if e.degree ≤ 2 then P.coeff e else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

theorem totalDegree_quadraticTruncation {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (quadraticTruncation P).totalDegree ≤ 2 := by
  classical
  apply Finset.sup_le
  intro e he
  have hn : (quadraticTruncation P).coeff e ≠ 0 := mem_support_iff.mp he
  rw [coeff_quadraticTruncation] at hn
  by_cases h : e.degree ≤ 2
  · exact h
  · simp only [h, ↓reduceIte, ne_eq, not_true_eq_false] at hn

theorem exists_monomial_predecessor {n : ℕ} (e : Fin n →₀ ℕ) (he : 0 < e.degree) :
    ∃ (i : Fin n) (m : Fin n →₀ ℕ),
      m + Finsupp.single i 1 = e ∧ m.degree + 1 = e.degree := by
  classical
  have hne : e ≠ 0 := by
    intro hz
    simp only [hz, map_zero] at he
    omega
  have hsome : ∃ i, e i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hne (Finsupp.ext hn)
  obtain ⟨i, hi⟩ := hsome
  let m := e - Finsupp.single i 1
  have hle : Finsupp.single i 1 ≤ e :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hid : m + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  refine ⟨i, m, hid, ?_⟩
  have hdeg := congrArg Finsupp.degree hid
  simpa only [map_add, Finsupp.degree_single] using hdeg

theorem abs_coeff_le_abs_pderiv_coeff {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (i : Fin n) (m : Fin n →₀ ℕ) :
    |P.coeff (m + Finsupp.single i 1)| ≤ |(pderiv i P).coeff m| := by
  rw [coeff_pderiv, abs_mul]
  have hcast : (0 : ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m i : ℝ) + 1)]
  nlinarith [abs_nonneg (P.coeff (m + Finsupp.single i 1))]

theorem high_coeff_le_of_third_partial_coeffs {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (E : ℝ)
    (hthird : ∀ (i j k : Fin n) (m : Fin n →₀ ℕ),
      |(pderiv i (pderiv j (pderiv k P))).coeff m| ≤ E)
    (e : Fin n →₀ ℕ) (he : 2 < e.degree) : |P.coeff e| ≤ E := by
  obtain ⟨k, e₁, he₁, hd₁⟩ := exists_monomial_predecessor e (by omega)
  obtain ⟨j, e₂, he₂, hd₂⟩ := exists_monomial_predecessor e₁ (by omega)
  obtain ⟨i, e₃, he₃, hd₃⟩ := exists_monomial_predecessor e₂ (by omega)
  calc
    |P.coeff e| ≤ |(pderiv k P).coeff e₁| := by
      rw [← he₁]
      exact abs_coeff_le_abs_pderiv_coeff P k e₁
    _ ≤ |(pderiv j (pderiv k P)).coeff e₂| := by
      rw [← he₂]
      exact abs_coeff_le_abs_pderiv_coeff (pderiv k P) j e₂
    _ ≤ |(pderiv i (pderiv j (pderiv k P))).coeff e₃| := by
      rw [← he₃]
      exact abs_coeff_le_abs_pderiv_coeff (pderiv j (pderiv k P)) i e₃
    _ ≤ E := hthird i j k e₃

/-- Fixed-degree third partial bounds give a quadratic approximation on
any finite-dimensional normalized box. The polynomial is the actual
coefficient truncation, so its low coefficients are unchanged. -/
theorem exists_quadratic_truncation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ),
      P.totalDegree ≤ D → ∀ E : ℝ, 0 ≤ E →
      (∀ (i j k : Fin n) (z : Fin n → ℝ), z ∈ Icc (-1) 1 →
        |eval z (pderiv i (pderiv j (pderiv k P)))| ≤ E) →
      (quadraticTruncation P).totalDegree ≤ 2 ∧
      ∀ z ∈ Icc (-1 : Fin n → ℝ) 1,
        |eval z P - eval z (quadraticTruncation P)| ≤ C ^ n * E := by
  obtain ⟨C, hC, hcoef⟩ := exists_multivariate_coefficient_constant D
  refine ⟨((D : ℝ) + 3) * C, by positivity, ?_⟩
  intro n P hP E hE hthird
  refine ⟨totalDegree_quadraticTruncation P, ?_⟩
  have hpd (Q : MvPolynomial (Fin n) ℝ) (i : Fin n) :
      (pderiv i Q).totalDegree ≤ Q.totalDegree :=
    (totalDegree_pderiv_le Q i).trans (Nat.sub_le _ _)
  have hthirdCoef (i j k : Fin n) (m : Fin n →₀ ℕ) :
      |(pderiv i (pderiv j (pderiv k P))).coeff m| ≤ C ^ n * E := by
    apply hcoef n _ ((hpd _ i).trans ((hpd _ j).trans ((hpd _ k).trans hP))) E hE
    intro z hz
    apply hthird i j k z
    refine ⟨?_, hz.2⟩
    intro i
    change -1 ≤ z i
    have hi : 0 ≤ z i := hz.1 i
    linarith
  let R := P - quadraticTruncation P
  have hR : R.totalDegree ≤ D + 2 := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    exact max_le (hP.trans (Nat.le_add_right _ _))
      ((totalDegree_quadraticTruncation P).trans (Nat.le_add_left _ _))
  have hRcoef (e : Fin n →₀ ℕ) : |R.coeff e| ≤ C ^ n * E := by
    dsimp only [R]
    rw [coeff_sub, coeff_quadraticTruncation]
    by_cases he : e.degree ≤ 2
    · simp only [he, ↓reduceIte, sub_self, abs_zero]
      positivity
    · simp only [he, ↓reduceIte, sub_zero]
      exact high_coeff_le_of_third_partial_coeffs P (C ^ n * E) hthirdCoef e (by omega)
  intro z hz
  have hmass := Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientMass.coefficientMass_le_of_coeff_bound
    R hR (by positivity : 0 ≤ C ^ n * E) hRcoef
  have heval := (eval_le_coefficientMass_on_unit R z hz).trans hmass
  change |eval z (P - quadraticTruncation P)| ≤ _ at heval
  rw [map_sub] at heval
  convert heval using 1
  push_cast
  rw [mul_pow]
  ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
