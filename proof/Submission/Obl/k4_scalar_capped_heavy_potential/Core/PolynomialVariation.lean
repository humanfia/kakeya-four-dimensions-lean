/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/PolynomialVariation.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/PolynomialVariation.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/PolynomialVariation.lean.
-/

import Submission.Lib.K4ScalarSwitching.MinorSublevel
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

open Set MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Lib.K4PolynomialPotential
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

/-- The fixed-point interpolation derivative bound is uniform on the
whole unit interval: at each point, a one-sided interval of length one half
stays inside the domain where the polynomial is bounded. -/
theorem exists_uniform_polynomial_derivative_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℝ), p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
        ∀ x ∈ Icc (0 : ℝ) 1, |p.derivative.eval x| ≤ C * E := by
  obtain ⟨C, hC, hderiv⟩ := exists_polynomial_derivative_constant D 0
  refine ⟨2 * C, by positivity, ?_⟩
  intro p hp E hE hb x hx
  let m : ℝ := if x ≤ 1 / 2 then 1 / 2 else -1 / 2
  let a : Polynomial ℝ := Polynomial.C x + Polynomial.C m * Polynomial.X
  let q := p.comp a
  have hma : |m| = 1 / 2 := by dsimp [m]; split_ifs <;> norm_num
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + m * t ∈ Icc (0 : ℝ) 1 := by
    dsimp [m]
    split_ifs with hh
    · constructor <;> linarith [hx.1, ht.1, ht.2]
    · constructor <;> linarith [hx.2, ht.1, ht.2]
  have hq : q.natDegree ≤ D := by
    have ha : a.natDegree ≤ 1 := by
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
        (Polynomial.natDegree_mul_le.trans (by simp)))
    exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hp ha).trans_eq (Nat.mul_one D))
  have hqb : ∀ t ∈ Icc (0 : ℝ) 1, |q.eval t| ≤ E := by
    intro t ht
    simpa [q, a] using hb (x + m * t) (hm t ht)
  have h := hderiv q hq E hE hqb
  have hd : q.derivative.eval 0 = p.derivative.eval x * m := by
    simp [q, a, Polynomial.derivative_comp]
    ring
  rw [hd, abs_mul, hma] at h
  nlinarith

/-- A coordinate-line variation bound with a degree-only constant,
independent of the polynomial coefficients and the ambient dimension. -/
theorem exists_coordinate_variation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
        (∀ z ∈ Icc (0 : Fin n → ℝ) 1, |eval z P| ≤ E) →
        ∀ x ∈ Icc (0 : Fin n → ℝ) 1, ∀ (i : Fin n) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
          |eval (Function.update x i t) P - eval x P| ≤ C * E * |t - x i| := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_polynomial_derivative_constant D
  refine ⟨C, hC, ?_⟩
  intro n P hP E hE hb x hx i t ht
  let q := coordinatePolynomialHom x i P
  have hq : q.natDegree ≤ D := by
    change (MvPolynomial.aeval
      (fun k => if k = i then Polynomial.X else Polynomial.C (x k)) P).natDegree ≤ D
    simpa only [Nat.mul_one] using MvPolynomial.aeval_natDegree_le (n := 1) P hP
      (fun k => if k = i then Polynomial.X else Polynomial.C (x k))
      (fun k => by split_ifs <;> simp)
  have hqb : ∀ s ∈ Icc (0 : ℝ) 1, |q.eval s| ≤ E := by
    intro s hs
    rw [eval_coordinatePolynomialHom]
    apply hb
    constructor <;> intro k <;> by_cases hk : k = i
    · subst k; simpa using hs.1
    · simpa [Function.update, hk] using hx.1 k
    · subst k; simpa using hs.2
    · simpa [Function.update, hk] using hx.2 k
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (0 : ℝ) 1) (x := x i) (y := t)
    (f := fun s => q.eval s) (f' := fun s => q.derivative.eval s)
    (fun s _ => (q.hasDerivAt s).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hbound q hq E hE hqb s hs)
    (convex_Icc _ _) ⟨hx.1 i, hx.2 i⟩ ht
  have hxi : q.eval (x i) = eval x P := by
    rw [eval_coordinatePolynomialHom, Function.update_eq_self]
  simpa only [Real.norm_eq_abs, q, eval_coordinatePolynomialHom,
    Function.update_eq_self] using h

/-- A bounded-degree polynomial bounded on a square varies by at most a
degree-only constant times its sup norm and the coordinate distance. -/
theorem exists_unit_square_variation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
        (∀ z ∈ Icc (0 : Fin 2 → ℝ) 1, |eval z P| ≤ E) →
        ∀ x ∈ Icc (0 : Fin 2 → ℝ) 1, ∀ y ∈ Icc (0 : Fin 2 → ℝ) 1,
          |eval y P - eval x P| ≤ C * E * (|y 0 - x 0| + |y 1 - x 1|) := by
  obtain ⟨C, hC, hcoord⟩ := exists_coordinate_variation_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP E hE hb x hx y hy
  have h₀ := hcoord 2 P hP E hE hb x hx 0 (y 0) ⟨hy.1 0, hy.2 0⟩
  have h₁ := hcoord 2 P hP E hE hb y hy 1 (x 1) ⟨hx.1 1, hx.2 1⟩
  have heq : Function.update y 1 (x 1) = Function.update x 0 (y 0) := by
    ext i
    fin_cases i <;> simp
  rw [heq] at h₁
  have h₁' : |eval y P - eval (Function.update x 0 (y 0)) P| ≤ C * E * |y 1 - x 1| := by
    simpa only [abs_sub_comm] using h₁
  calc
    _ ≤ |eval y P - eval (Function.update x 0 (y 0)) P| +
        |eval (Function.update x 0 (y 0)) P - eval x P| := abs_sub_le _ _ _
    _ ≤ C * E * |y 1 - x 1| + C * E * |y 0 - x 0| := add_le_add h₁' h₀
    _ = C * E * (|y 0 - x 0| + |y 1 - x 1|) := by ring

/-- The same uniform variation control on the normalized symmetric box
used by the switched polynomial field. -/
theorem exists_symmetric_square_variation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
        (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ E) →
        ∀ x ∈ Icc (-1 : Fin 2 → ℝ) 1, ∀ y ∈ Icc (-1 : Fin 2 → ℝ) 1,
          |eval y P - eval x P| ≤ C * E * (|y 0 - x 0| + |y 1 - x 1|) := by
  obtain ⟨C, hC, hunit⟩ := exists_unit_square_variation_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP E hE hb x hx y hy
  let Q : MvPolynomial (Fin 2) ℝ := aeval (fun i => MvPolynomial.C (2 : ℝ) * X i - 1) P
  have hQ : Q.totalDegree ≤ D := by
    apply (degree_aeval_le P _ ?_).trans hP
    intro i
    apply degree_sub_le
    · exact (degree_C_mul_le _ _).trans (by simp)
    · simp
  have heval (z : Fin 2 → ℝ) : eval z Q = eval (fun i => 2 * z i - 1) P := by
    dsimp only [Q]
    rw [eval_substitution]
    simp only [map_sub, map_mul, eval_C, eval_X, map_one]
  have hQb : ∀ z ∈ Icc (0 : Fin 2 → ℝ) 1, |eval z Q| ≤ E := by
    intro z hz
    rw [heval]
    apply hb
    constructor <;> intro i
    · have h := hz.1 i
      change (0 : ℝ) ≤ z i at h
      change (-1 : ℝ) ≤ 2 * z i - 1
      linarith
    · have h := hz.2 i
      change z i ≤ (1 : ℝ) at h
      change 2 * z i - 1 ≤ (1 : ℝ)
      linarith
  have hnorm (z : Fin 2 → ℝ) (hz : z ∈ Icc (-1 : Fin 2 → ℝ) 1) :
      (fun i => (z i + 1) / 2) ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    constructor <;> intro i
    · have h := hz.1 i
      change (-1 : ℝ) ≤ z i at h
      change (0 : ℝ) ≤ (z i + 1) / 2
      linarith
    · have h := hz.2 i
      change z i ≤ (1 : ℝ) at h
      change (z i + 1) / 2 ≤ (1 : ℝ)
      linarith
  have hback (z : Fin 2 → ℝ) : eval (fun i => (z i + 1) / 2) Q = eval z P := by
    rw [heval]
    apply congrArg (fun f : Fin 2 → ℝ => eval f P)
    ext i
    ring
  have h := hunit Q hQ E hE hQb _ (hnorm x hx) _ (hnorm y hy)
  rw [hback, hback] at h
  have hd (i : Fin 2) : |(y i + 1) / 2 - (x i + 1) / 2| = |y i - x i| / 2 := by
    rw [show (y i + 1) / 2 - (x i + 1) / 2 = (y i - x i) / 2 by ring, abs_div]
    norm_num
  simp only [hd] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hE)
  linarith [abs_nonneg (y 0 - x 0), abs_nonneg (y 1 - x 1)]

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
