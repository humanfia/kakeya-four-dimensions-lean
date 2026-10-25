/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/FourDirections.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/FourDirections.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientBounds
import Submission.Lib.K4ScalarSwitching.Switching
import Submission.Lib.K4PolynomialPotential.TrajectoryFits

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set MvPolynomial

/-- Four separated samples control a cubic on the normalized interval;
the six powers pay for three numerators and three inverse separations. -/
theorem cubic_bound_of_four_separated_values (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 3) (v : Fin 4 → ℝ) (K E : ℝ)
    (hK : 1 ≤ K) (hE : 0 ≤ E)
    (hv : ∀ i, |v i| ≤ K)
    (hsep : ∀ i j, i ≠ j → 1 / K ≤ |v i - v j|)
    (hsample : ∀ i, |p.eval (v i)| ≤ E) :
    ∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ 32 * K ^ 6 * E := by
  classical
  have hKp : 0 < K := by linarith
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, sub_self, abs_zero] at h
    have : 0 < 1 / K := one_div_pos.mpr hKp
    linarith
  have hdeg : p.degree < (Finset.univ : Finset (Fin 4)).card := by
    apply lt_of_le_of_lt p.degree_le_natDegree
    norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot, WithBot.coe_lt_coe]
    omega
  have hformula := Lagrange.eq_interpolate (s := Finset.univ) hinj.injOn hdeg
  intro t ht
  have hfactor (i j : Fin 4) (hij : i ≠ j) :
      |(Lagrange.basisDivisor (v i) (v j)).eval t| ≤ 2 * K ^ 2 := by
    have hd : 0 < |v i - v j| := (one_div_pos.mpr hKp).trans_le (hsep i j hij)
    have hinv : |v i - v j|⁻¹ ≤ K :=
      (inv_le_comm₀ hd hKp).mpr (by simpa only [one_div] using hsep i j hij)
    have hnum : |t - v j| ≤ 2 * K := by
      have habs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have hh := abs_sub t (v j)
      linarith [hv j]
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X, abs_mul, abs_inv]
    have h := mul_le_mul hinv hnum (abs_nonneg _) (le_of_lt hKp)
    nlinarith
  have hb (i : Fin 4) : |(Lagrange.basis Finset.univ v i).eval t| ≤ 8 * K ^ 6 := by
    rw [Lagrange.basis, Polynomial.eval_prod, Finset.abs_prod]
    calc
      _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin 4)).erase i, (2 * K ^ 2) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact abs_nonneg _
        · intro j hj
          exact hfactor i j (Finset.mem_erase.mp hj).1.symm
      _ = 8 * K ^ 6 := by simp; ring
  have heval : p.eval t =
      ∑ i : Fin 4, p.eval (v i) * (Lagrange.basis Finset.univ v i).eval t := by
    conv_lhs => rw [hformula]
    simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
  rw [heval]
  calc
    _ ≤ ∑ i : Fin 4, |p.eval (v i) * (Lagrange.basis Finset.univ v i).eval t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, E * (8 * K ^ 6) := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (hsample i) (hb i) (abs_nonneg _) hE
    _ = 32 * K ^ 6 * E := by simp; ring

/-- The affine-line directional derivative in the time-position plane. -/
noncomputable def directionalPartial (v : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ := pderiv 0 P + C v * pderiv 1 P

theorem directionalPartial_cube (P : MvPolynomial (Fin 2) ℝ) (v : ℝ) :
    directionalPartial v (directionalPartial v (directionalPartial v P)) =
      pderiv 0 (pderiv 0 (pderiv 0 P)) +
      C (3 * v) * pderiv 0 (pderiv 0 (pderiv 1 P)) +
      C (3 * v ^ 2) * pderiv 0 (pderiv 1 (pderiv 1 P)) +
      C (v ^ 3) * pderiv 1 (pderiv 1 (pderiv 1 P)) := by
  simp only [directionalPartial, map_add, pderiv_C_mul]
  simp only [partials_commute P 1 0, partials_commute (pderiv 0 P) 1 0,
    partials_commute (pderiv 1 P) 1 0]
  simp only [map_mul, map_ofNat, map_pow]
  ring

noncomputable def thirdDirectionPolynomial (P : MvPolynomial (Fin 2) ℝ)
    (z : Fin 2 → ℝ) : Polynomial ℝ :=
  Polynomial.C (eval z (pderiv 0 (pderiv 0 (pderiv 0 P)))) +
    Polynomial.C (3 * eval z (pderiv 0 (pderiv 0 (pderiv 1 P)))) * Polynomial.X +
    Polynomial.C (3 * eval z (pderiv 0 (pderiv 1 (pderiv 1 P)))) * Polynomial.X ^ 2 +
    Polynomial.C (eval z (pderiv 1 (pderiv 1 (pderiv 1 P)))) * Polynomial.X ^ 3

theorem eval_thirdDirectionPolynomial (P : MvPolynomial (Fin 2) ℝ)
    (z : Fin 2 → ℝ) (v : ℝ) :
    (thirdDirectionPolynomial P z).eval v =
      eval z (directionalPartial v (directionalPartial v (directionalPartial v P))) := by
  rw [directionalPartial_cube]
  simp only [thirdDirectionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_add, map_mul, eval_C]
  ring

theorem natDegree_thirdDirectionPolynomial (P : MvPolynomial (Fin 2) ℝ)
    (z : Fin 2 → ℝ) : (thirdDirectionPolynomial P z).natDegree ≤ 3 := by
  unfold thirdDirectionPolynomial
  compute_degree

/-- Four separated time-position directions determine every third partial.
The directions may be chosen separately at each base point. -/
theorem exists_four_direction_third_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
      (v : Fin 4 → ℝ) (K E : ℝ), 1 ≤ K → 0 ≤ E →
      (∀ i, |v i| ≤ K) →
      (∀ i j, i ≠ j → 1 / K ≤ |v i - v j|) →
      (∀ i, |eval z (directionalPartial (v i)
        (directionalPartial (v i) (directionalPartial (v i) P)))| ≤ E) →
      ∀ i j k : Fin 2,
        |eval z (pderiv i (pderiv j (pderiv k P)))| ≤ C * K ^ 6 * E := by
  obtain ⟨C, hC, hcoeff⟩ := exists_univariate_coefficient_constant 3
  refine ⟨32 * C, by positivity, ?_⟩
  intro P z v K E hK hE hv hsep hthird
  let q := thirdDirectionPolynomial P z
  have hq : q.natDegree ≤ 3 := natDegree_thirdDirectionPolynomial P z
  have hqE : 0 ≤ 32 * K ^ 6 * E := by positivity
  have hsup : ∀ t ∈ Icc (0 : ℝ) 1, |q.eval t| ≤ 32 * K ^ 6 * E :=
    cubic_bound_of_four_separated_values q hq v K E hK hE hv hsep
      (fun i => by simpa only [q, eval_thirdDirectionPolynomial] using hthird i)
  have hcoef (k : ℕ) : |q.coeff k| ≤ (32 * C) * K ^ 6 * E := by
    convert hcoeff q hq _ hqE hsup k using 1 <;> ring
  have hc0 : q.coeff 0 = eval z (pderiv 0 (pderiv 0 (pderiv 0 P))) := by
    simp only [q, thirdDirectionPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hc1 : q.coeff 1 = 3 * eval z (pderiv 0 (pderiv 0 (pderiv 1 P))) := by
    simp only [q, thirdDirectionPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hc2 : q.coeff 2 = 3 * eval z (pderiv 0 (pderiv 1 (pderiv 1 P))) := by
    simp only [q, thirdDirectionPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hc3 : q.coeff 3 = eval z (pderiv 1 (pderiv 1 (pderiv 1 P))) := by
    simp only [q, thirdDirectionPolynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have h0 := hcoef 0
  rw [hc0] at h0
  have h1 : |eval z (pderiv 0 (pderiv 0 (pderiv 1 P)))| ≤ (32 * C) * K ^ 6 * E := by
    have h := hcoef 1
    rw [hc1, abs_mul] at h
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h
    linarith [abs_nonneg (eval z (pderiv 0 (pderiv 0 (pderiv 1 P))))]
  have h2 : |eval z (pderiv 0 (pderiv 1 (pderiv 1 P)))| ≤ (32 * C) * K ^ 6 * E := by
    have h := hcoef 2
    rw [hc2, abs_mul] at h
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h
    linarith [abs_nonneg (eval z (pderiv 0 (pderiv 1 (pderiv 1 P))))]
  have h3 := hcoef 3
  rw [hc3] at h3
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact h0
  · exact h1
  · change |eval z (pderiv 0 (pderiv 1 (pderiv 0 P)))| ≤ _
    rw [partials_commute P 1 0]
    exact h1
  · exact h2
  · change |eval z (pderiv 1 (pderiv 0 (pderiv 0 P)))| ≤ _
    rw [partials_commute (pderiv 0 P) 1 0, partials_commute P 1 0]
    exact h1
  · change |eval z (pderiv 1 (pderiv 0 (pderiv 1 P)))| ≤ _
    rw [partials_commute (pderiv 1 P) 1 0]
    exact h2
  · change |eval z (pderiv 1 (pderiv 1 (pderiv 0 P)))| ≤ _
    rw [partials_commute P 1 0, partials_commute (pderiv 1 P) 1 0]
    exact h2
  · exact h3

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Lib.K4PolynomialPotential

theorem derivative_scalarLineHom_directional (P : MvPolynomial (Fin 2) ℝ) (u v : ℝ) :
    (scalarLineHom u v P).derivative = scalarLineHom u v (directionalPartial v P) := by
  rw [derivative_scalarLineHom]
  simp [directionalPartial, map_add, map_mul, scalarLineHom]

theorem third_derivative_scalarLineHom (P : MvPolynomial (Fin 2) ℝ) (u v t : ℝ) :
    (scalarLineHom u v P).derivative.derivative.derivative.eval t =
      MvPolynomial.eval ![t, u + t * v]
        (directionalPartial v (directionalPartial v (directionalPartial v P))) := by
  rw [derivative_scalarLineHom_directional, derivative_scalarLineHom_directional,
    derivative_scalarLineHom_directional, eval_scalarLineHom]

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
