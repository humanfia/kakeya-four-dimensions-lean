/-
Adapted from: here:o062
Purpose: Shared scalar switching helper MinorSublevel.
Original owned source: x0511, commit 4a7e8db, Submission/Obl/k4_scalar_mesh_projection/MinorSublevel.lean.
-/

/-
Local LOT source: session x0511, branch x0511, commit 4a7e8db,
Submission/Obl/k4_scalar_mesh_projection/MinorSublevel.lean.
Reviewed and integrated by x0212 for o062.
-/

import Submission.Lib.K4ScalarSwitching.TensorRemez
import Submission.Lib.K4ScalarSwitching.Switching
import Submission.Lib.K4ScalarSwitching.SwitchPathBounds

namespace Submission.Lib.K4ScalarSwitching.Switching
open Set Polynomial MeasureTheory
open Submission.Lib.K4PolynomialPotential

theorem exists_polynomial_derivative_constant (D : ℕ) (x : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℝ), p.natDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E → (∀ t ∈ Icc (0 : ℝ) 1, |p.eval t| ≤ E) →
        |p.derivative.eval x| ≤ C * E := by
  classical
  let v : Fin (D + 1) → ℝ := fun k => (k : ℝ) / ((D : ℝ) + 1)
  have hden : 0 < (D : ℝ) + 1 := by positivity
  have hv : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    have hcast : (i : ℝ) = (j : ℝ) :=
      (div_left_inj' hden.ne').mp hij
    exact_mod_cast hcast
  have hvi (i : Fin (D + 1)) : v i ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hden.le
    · apply (div_le_one hden).mpr
      have hi : i.val ≤ D + 1 := Nat.le_of_lt i.isLt
      exact_mod_cast hi
  let W : Fin (D + 1) → ℝ := fun i =>
    |(Lagrange.basis Finset.univ v i).derivative.eval x|
  refine ⟨1 + ∑ i, W i, by
    have : 0 ≤ ∑ i, W i := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith, ?_⟩
  intro p hp E hE hb
  have hdeg : p.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    apply lt_of_le_of_lt p.degree_le_natDegree
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_withBot,
      WithBot.coe_lt_coe]
    omega
  have heq := Lagrange.eq_interpolate (s := Finset.univ) hv.injOn hdeg
  have hformula : p.derivative.eval x =
      ∑ i, p.eval (v i) * (Lagrange.basis Finset.univ v i).derivative.eval x := by
    conv_lhs => rw [heq]
    simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  rw [hformula]
  calc
    |∑ i, p.eval (v i) * (Lagrange.basis Finset.univ v i).derivative.eval x|
      ≤ ∑ i, |p.eval (v i) * (Lagrange.basis Finset.univ v i).derivative.eval x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, E * W i := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb _ (hvi i)) (abs_nonneg _)
    _ = (∑ i, W i) * E := by rw [← Finset.mul_sum]; ring
    _ ≤ (1 + ∑ i, W i) * E := by gcongr; linarith

/-- The linear coefficients of a bounded-degree polynomial are bounded by
its sup norm on the unit cube, with a constant depending only on the degree. -/
theorem exists_linear_coefficient_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ D →
      ∀ E : ℝ, 0 ≤ E →
        (∀ z ∈ Icc (0 : Fin 4 → ℝ) 1, |MvPolynomial.eval z P| ≤ E) →
        ∀ i : Fin 4, |P.coeff (Finsupp.single i 1)| ≤ C * E := by
  obtain ⟨C, hC, hbound⟩ := exists_polynomial_derivative_constant D 0
  refine ⟨C, hC, ?_⟩
  intro P hP E hE hb i
  let q := coordinatePolynomialHom (0 : Fin 4 → ℝ) i P
  have hq : q.natDegree ≤ D := by
    change (MvPolynomial.aeval
      (fun k => if k = i then Polynomial.X else Polynomial.C (0 : ℝ)) P).natDegree ≤ D
    simpa only [Nat.mul_one] using MvPolynomial.aeval_natDegree_le (n := 1) P hP
      (fun k : Fin 4 => if k = i then Polynomial.X else Polynomial.C (0 : ℝ))
      (fun k => by split_ifs <;> simp)
  have hqb : ∀ t ∈ Icc (0 : ℝ) 1, |q.eval t| ≤ E := by
    intro t ht
    rw [eval_coordinatePolynomialHom]
    apply hb
    constructor <;> intro k <;> by_cases hk : k = i <;>
      simp [Function.update, hk, ht.1, ht.2]
  have h := hbound q hq E hE hqb
  change |(coordinatePolynomialHom (0 : Fin 4 → ℝ) i P).derivative.eval 0| ≤ C * E at h
  rw [derivative_coordinatePolynomialHom, eval_coordinatePolynomialHom] at h
  have hz : Function.update (0 : Fin 4 → ℝ) i 0 = 0 := by ext k; simp
  simpa only [hz, partial_eval_zero_eq_coeff] using h

/-- A large linear coefficient forces the small-value set of a polynomial
to have small four-dimensional volume. The threshold is an explicit power
of the allowed exceptional volume. -/
theorem exists_polynomial_sublevel_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ D →
      ∀ (i : Fin 4) (κ η : ℝ), 0 < κ → 0 < η → η ≤ 1 →
        κ ≤ |P.coeff (Finsupp.single i 1)| →
        volume {z : Fin 4 → ℝ | z ∈ Icc (0 : Fin 4 → ℝ) 1 ∧
          |MvPolynomial.eval z P| ≤
            κ * η ^ (4 * D) / (2 * C * (32 * ((D : ℝ) + 1)) ^ (4 * D))} <
              ENNReal.ofReal η := by
  obtain ⟨C, hC, hcoeff⟩ := exists_linear_coefficient_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP i κ η hκ hη hη1 hi
  let E : ℝ := κ * η ^ (4 * D) / (2 * C * (32 * ((D : ℝ) + 1)) ^ (4 * D))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let S : Set (Fin 4 → ℝ) := {z | z ∈ Icc 0 1 ∧ |MvPolynomial.eval z P| ≤ E}
  have hSm : MeasurableSet S := measurableSet_Icc.inter
    (isClosed_le (MvPolynomial.continuous_eval P).abs continuous_const).measurableSet
  by_contra! hvol
  have hremez := polynomial_remez_four P D hP S hSm hη hη1 hE
    (fun _ hz => hz.1) hvol (fun _ hz => hz.2)
  have h := hcoeff P hP _ (by positivity) hremez i
  have hden : 32 * ((D : ℝ) + 1) ≠ 0 := by positivity
  have hid : C * ((32 * ((D : ℝ) + 1) / η) ^ (4 * D) * E) = κ / 2 := by
    dsimp [E]
    rw [div_pow]
    field_simp
  rw [hid] at h
  linarith

/-- At a high-curl start, one of the actual maximal endpoint minors has a
small exceptional set. The degree-only constant is uniform in the rows,
the starting point and all four velocities. -/
theorem exists_switching_sublevel_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (K κ η : ℝ),
        1 ≤ K → 0 < κ → 0 < η → η ≤ 1 →
        (∀ i, |v i| ≤ K) → 1 / K ≤ |v 1 - v 0| → 1 / K ≤ |v 3 - v 2| →
        8 * K ^ 4 * κ < |MvPolynomial.eval x (MvPolynomial.pderiv 0 B - MvPolynomial.pderiv 1 A)| →
        ∃ j : Fin 4, 2 ≤ j.val ∧
          volume {δ : Fin 4 → ℝ | δ ∈ Icc (0 : Fin 4 → ℝ) 1 ∧
            |MvPolynomial.eval δ (endpointMinor (brokenHeight A B x v) v j)| ≤
              κ * η ^ (4 * D) / (2 * C * (32 * ((D : ℝ) + 1)) ^ (4 * D))} <
                ENNReal.ofReal η := by
  obtain ⟨C, hC, hsub⟩ := exists_polynomial_sublevel_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB x v K κ η hK hκ hη hη1 hv hI hJ hcurl
  obtain ⟨i, j, _, hj, hi⟩ := exists_large_minor_coefficient A B x v
    hK hκ.le hv hI hJ hcurl
  refine ⟨j, hj, hsub _ ?_ i κ η hκ hη hη1 hi.le⟩
  exact (brokenHeight_minor_degree A B x v j).trans (max_le hA hB)

end Submission.Lib.K4ScalarSwitching.Switching
