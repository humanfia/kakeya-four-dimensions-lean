/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/QuadraticFromLines.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/QuadraticFromLines.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.FourDirections
import Submission.Lib.K4ScalarCoreTools.Simulation.SymmetricDerivatives
import Submission.Lib.K4ScalarCoreTools.Simulation.ThirdJetRestoration
import Submission.Lib.K4ScalarCoreTools.Simulation.BaseSublevel

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- A whole-line quadratic fit controls the actual third directional
derivative of the common polynomial field. -/
theorem exists_third_bound_of_quadratic_fit_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ (S : Polynomial ℝ), S.natDegree ≤ 2 → ∀ u v E : ℝ, 0 ≤ E →
      (∀ t ∈ Icc (-1 : ℝ) 1, |eval ![t, u + t * v] P - S.eval t| ≤ E) →
      ∀ t ∈ Icc (-1 : ℝ) 1,
        |eval ![t, u + t * v] (directionalPartial v
          (directionalPartial v (directionalPartial v P)))| ≤ C * E := by
  obtain ⟨C, hC, hthird⟩ := exists_symmetric_polynomial_third_constant (D + 2)
  refine ⟨C, hC, ?_⟩
  intro P hP S hS u v E hE hfit t ht
  let q := scalarLineHom u v P - S
  have hq : q.natDegree ≤ D + 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le ((natDegree_scalarLineHom_le P u v).trans (hP.trans (Nat.le_add_right _ _)))
      (hS.trans (Nat.le_add_left _ _))
  have hqfit : ∀ s ∈ Icc (-1 : ℝ) 1, |q.eval s| ≤ E := by
    intro s hs
    simpa only [q, Polynomial.eval_sub, eval_scalarLineHom] using hfit s hs
  have hzero : S.derivative.derivative.derivative = 0 :=
    Polynomial.iterate_derivative_eq_zero (by omega : S.natDegree < 3)
  have h := hthird q hq E hE hqfit t ht
  simpa only [q, Polynomial.derivative_sub, Polynomial.eval_sub, hzero,
    Polynomial.eval_zero, sub_zero, third_derivative_scalarLineHom] using h

/-- A common bounded-degree polynomial with quadratic fits along four
separated lines through every base point is uniformly close to a single
quadratic. The four lines may vary with the base point. -/
theorem exists_quadratic_restoration_from_lines_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K E : ℝ, 1 ≤ K → 0 ≤ E →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
        ∃ (v u : Fin 4 → ℝ) (S : Fin 4 → Polynomial ℝ),
          (∀ i, |v i| ≤ K) ∧
          (∀ i j, i ≠ j → 1 / K ≤ |v i - v j|) ∧
          (∀ i, z 1 = u i + z 0 * v i ∧ (S i).natDegree ≤ 2 ∧
            ∀ t ∈ Icc (-1 : ℝ) 1, |eval ![t, u i + t * v i] P - (S i).eval t| ≤ E)) →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ e : Fin 2 →₀ ℕ, e.degree ≤ 2 → Q.coeff e = P.coeff e) ∧
        ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P - eval z Q| ≤ C * K ^ 6 * E := by
  obtain ⟨Cline, hCline, hline⟩ := exists_third_bound_of_quadratic_fit_constant D
  obtain ⟨Cdir, hCdir, hdir⟩ := exists_four_direction_third_constant
  obtain ⟨Cquad, hCquad, hquad⟩ := exists_quadratic_truncation_constant D
  refine ⟨Cquad ^ 2 * Cdir * Cline, by positivity, ?_⟩
  intro P hP K E hK hE hlines
  have hthird (i j k : Fin 2) (z : Fin 2 → ℝ) (hz : z ∈ Icc (-1 : Fin 2 → ℝ) 1) :
      |eval z (pderiv i (pderiv j (pderiv k P)))| ≤ Cdir * K ^ 6 * (Cline * E) := by
    obtain ⟨v, u, S, hv, hsep, hfits⟩ := hlines z hz
    apply hdir P z v K (Cline * E) hK (by positivity) hv hsep
    intro l
    obtain ⟨hpoint, hS, hfit⟩ := hfits l
    have hz0 : z 0 ∈ Icc (-1 : ℝ) 1 := ⟨hz.1 0, hz.2 0⟩
    have h := hline P hP (S l) hS (u l) (v l) E hE hfit (z 0) hz0
    have hid : (![z 0, u l + z 0 * v l] : Fin 2 → ℝ) = z := by
      ext d
      fin_cases d
      · rfl
      · exact hpoint.symm
    simpa only [hid] using h
  obtain ⟨hdegree, herror⟩ := hquad 2 P hP (Cdir * K ^ 6 * (Cline * E))
    (by positivity) hthird
  refine ⟨quadraticTruncation P, hdegree, ?_, ?_⟩
  · intro e he
    simp only [coeff_quadraticTruncation, he, ↓reduceIte]
  · intro z hz
    convert herror z hz using 1 <;> ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set MvPolynomial MeasureTheory
open Submission.Lib.K4PolynomialPotential

/-- The four-line test is needed only on a base set of positive area.
Remez transfers its third-jet control before the common quadratic is
restored; the successful base set is never normalized. -/
theorem exists_quadratic_restoration_from_base_lines_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K E η : ℝ, 1 ≤ K → 0 ≤ E → 0 < η → η ≤ 1 →
      ∀ S : Set (Fin 2 → ℝ), S ⊆ Icc (-1 : Fin 2 → ℝ) 1 →
      ENNReal.ofReal η ≤ volume S →
      (∀ z ∈ S, ∃ (v u : Fin 4 → ℝ) (T : Fin 4 → Polynomial ℝ),
        (∀ i, |v i| ≤ K) ∧
        (∀ i j, i ≠ j → 1 / K ≤ |v i - v j|) ∧
        (∀ i, z 1 = u i + z 0 * v i ∧ (T i).natDegree ≤ 2 ∧
          ∀ t ∈ Icc (-1 : ℝ) 1, |eval ![t, u i + t * v i] P - (T i).eval t| ≤ E)) →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ e : Fin 2 →₀ ℕ, e.degree ≤ 2 → Q.coeff e = P.coeff e) ∧
        ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P - eval z Q| ≤
          C * K ^ 6 * (64 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  obtain ⟨Cline, hCline, hline⟩ := exists_third_bound_of_quadratic_fit_constant D
  obtain ⟨Cdir, hCdir, hdir⟩ := exists_four_direction_third_constant
  obtain ⟨Cquad, hCquad, hquad⟩ := exists_quadratic_truncation_constant D
  refine ⟨Cquad ^ 2 * Cdir * Cline, by positivity, ?_⟩
  intro P hP K E η hK hE hη hη1 S hS hmass hlines
  let B := Cdir * K ^ 6 * (Cline * E)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hthirdS (i j k : Fin 2) (z : Fin 2 → ℝ) (hz : z ∈ S) :
      |eval z (pderiv i (pderiv j (pderiv k P)))| ≤ B := by
    obtain ⟨v, u, T, hv, hsep, hfits⟩ := hlines z hz
    apply hdir P z v K (Cline * E) hK (by positivity) hv hsep
    intro l
    obtain ⟨hpoint, hT, hfit⟩ := hfits l
    have hz0 : z 0 ∈ Icc (-1 : ℝ) 1 := ⟨(hS hz).1 0, (hS hz).2 0⟩
    have h := hline P hP (T l) hT (u l) (v l) E hE hfit (z 0) hz0
    have hid : (![z 0, u l + z 0 * v l] : Fin 2 → ℝ) = z := by
      ext d
      fin_cases d
      · rfl
      · exact hpoint.symm
    simpa only [hid] using h
  let F := (64 * ((D : ℝ) + 1) / η) ^ (2 * D)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpd (R : MvPolynomial (Fin 2) ℝ) (i : Fin 2) :
      (pderiv i R).totalDegree ≤ R.totalDegree :=
    (totalDegree_pderiv_le R i).trans (Nat.sub_le _ _)
  have hthird (i j k : Fin 2) : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z (pderiv i (pderiv j (pderiv k P)))| ≤ F * B :=
    polynomial_remez_symmetric_two _ D
      ((hpd _ i).trans ((hpd _ j).trans ((hpd _ k).trans hP)))
      S hη hη1 hB hS hmass (hthirdS i j k)
  obtain ⟨hdegree, herror⟩ := hquad 2 P hP (F * B) (mul_nonneg hF hB) hthird
  refine ⟨quadraticTruncation P, hdegree, ?_, ?_⟩
  · intro e he
    simp only [coeff_quadraticTruncation, he, ↓reduceIte]
  · intro z hz
    convert herror z hz using 1
    dsimp only [F, B]
    ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
