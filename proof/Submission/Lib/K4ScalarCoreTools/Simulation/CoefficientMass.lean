/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/CoefficientMass.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original leaf source: accepted here:o183, PolynomialBounds.lean, promoted by o062.
General coefficient-mass bounds are unchanged.
Its original here:o151/x0508 attribution is retained below.
-/

/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/PolynomialBounds.lean. Earlier provenance comments are retained. -/
import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientMass

open MvPolynomial

/-- The sum of absolute coefficients, used only for fixed-degree transport
estimates. It keeps all coefficient costs polynomial in the frame data. -/
noncomputable def coefficientMass {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ m ∈ P.support, |P.coeff m|

theorem coefficientMass_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    0 ≤ coefficientMass P := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem coefficientMass_eq_sum {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (S : Finset (Fin n →₀ ℕ)) (hS : P.support ⊆ S) :
    coefficientMass P = ∑ m ∈ S, |P.coeff m| := by
  classical
  apply Finset.sum_subset hS
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]

theorem abs_coeff_le_coefficientMass {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) : |P.coeff m| ≤ coefficientMass P := by
  classical
  by_cases hm : m ∈ P.support
  · exact Finset.single_le_sum (f := fun m : Fin n →₀ ℕ => |P.coeff m|)
      (fun _ _ => abs_nonneg _) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]
    exact coefficientMass_nonneg P

theorem coefficientMass_zero {n : ℕ} : coefficientMass (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [coefficientMass]

theorem coefficientMass_monomial {n : ℕ} (m : Fin n →₀ ℕ) (a : ℝ) :
    coefficientMass (monomial m a) = |a| := by
  classical
  rw [coefficientMass_eq_sum _ {m} MvPolynomial.support_monomial_subset]
  simp

theorem coefficientMass_C {n : ℕ} (a : ℝ) :
    coefficientMass (C a : MvPolynomial (Fin n) ℝ) = |a| := coefficientMass_monomial 0 a

theorem coefficientMass_X {n : ℕ} (i : Fin n) :
    coefficientMass (X i : MvPolynomial (Fin n) ℝ) = 1 := by
  change coefficientMass (monomial (Finsupp.single i 1) 1) = 1
  rw [coefficientMass_monomial, abs_one]

theorem coefficientMass_one {n : ℕ} : coefficientMass (1 : MvPolynomial (Fin n) ℝ) = 1 := by
  change coefficientMass (monomial 0 1) = 1
  rw [coefficientMass_monomial, abs_one]

theorem coefficientMass_add {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ) :
    coefficientMass (P + Q) ≤ coefficientMass P + coefficientMass Q := by
  classical
  rw [coefficientMass_eq_sum _ (P.support ∪ Q.support) MvPolynomial.support_add,
    coefficientMass_eq_sum P _ Finset.subset_union_left,
    coefficientMass_eq_sum Q _ Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _
  change |P.coeff m + Q.coeff m| ≤ |P.coeff m| + |Q.coeff m|
  exact abs_add_le _ _

theorem coefficientMass_sum {n : ℕ} {ι : Type*} (S : Finset ι)
    (P : ι → MvPolynomial (Fin n) ℝ) :
    coefficientMass (∑ i ∈ S, P i) ≤ ∑ i ∈ S, coefficientMass (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coefficientMass_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (coefficientMass_add _ _).trans (add_le_add le_rfl ih)

theorem coefficientMass_mul {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ) :
    coefficientMass (P * Q) ≤ coefficientMass P * coefficientMass Q := by
  classical
  rw [MvPolynomial.mul_def]
  simp only [MvPolynomial.sum_def]
  calc
    _ ≤ ∑ m ∈ P.support, coefficientMass
        (∑ s ∈ Q.support, monomial (m + s) (P.coeff m * Q.coeff s)) := coefficientMass_sum _ _
    _ ≤ ∑ m ∈ P.support, ∑ s ∈ Q.support,
        coefficientMass (monomial (m + s) (P.coeff m * Q.coeff s)) :=
      Finset.sum_le_sum fun m _ => coefficientMass_sum _ _
    _ = ∑ m ∈ P.support, ∑ s ∈ Q.support, |P.coeff m| * |Q.coeff s| := by
      simp only [coefficientMass_monomial, abs_mul]
    _ = _ := by
      rw [coefficientMass, coefficientMass, Finset.sum_mul]
      simp only [Finset.mul_sum]

theorem coefficientMass_pow {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (d : ℕ) :
    coefficientMass (P ^ d) ≤ coefficientMass P ^ d := by
  induction d with
  | zero => simp only [pow_zero, coefficientMass_one, le_refl]
  | succ d ih =>
    rw [pow_succ, pow_succ]
    exact (coefficientMass_mul _ _).trans
      (mul_le_mul_of_nonneg_right ih (coefficientMass_nonneg P))


theorem coefficientMass_neg {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    coefficientMass (-P) = coefficientMass P := by
  simp only [coefficientMass, MvPolynomial.support_neg, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, abs_neg]

theorem coefficientMass_sub {n : ℕ} (P Q : MvPolynomial (Fin n) ℝ) :
    coefficientMass (P - Q) ≤ coefficientMass P + coefficientMass Q := by
  simpa only [sub_eq_add_neg, coefficientMass_neg] using coefficientMass_add P (-Q)

theorem coefficientMass_prod {n : ℕ} {ι : Type*} (S : Finset ι)
    (P : ι → MvPolynomial (Fin n) ℝ) :
    coefficientMass (∏ i ∈ S, P i) ≤ ∏ i ∈ S, coefficientMass (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, coefficientMass_one, le_refl]
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (coefficientMass_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (coefficientMass_nonneg _))

/-- The affine substitution bound depends on the fixed degree, not on the
number of polynomial variables or on the requested subpower loss. -/
theorem coefficientMass_aeval {n m D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D)
    (f : Fin n → MvPolynomial (Fin m) ℝ) {H : ℝ} (hH : 1 ≤ H)
    (hf : ∀ i, coefficientMass (f i) ≤ H) :
    coefficientMass (aeval f P) ≤ coefficientMass P * H ^ D := by
  classical
  have hterm (e : Fin n →₀ ℕ) (he : e ∈ P.support) :
      coefficientMass (aeval f (monomial e (P.coeff e))) ≤ |P.coeff e| * H ^ D := by
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (by intro i; simp)]
    calc
      _ ≤ coefficientMass (C (P.coeff e)) * coefficientMass (∏ i, f i ^ e i) :=
        coefficientMass_mul _ _
      _ ≤ |P.coeff e| * (∏ i, coefficientMass (f i ^ e i)) := by
        rw [coefficientMass_C]
        exact mul_le_mul_of_nonneg_left (coefficientMass_prod _ _) (abs_nonneg _)
      _ ≤ |P.coeff e| * (∏ i, H ^ e i) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.prod_le_prod₀
        · intro i _; exact coefficientMass_nonneg _
        · intro i _
          exact (coefficientMass_pow _ _).trans
            (pow_le_pow_left₀ (coefficientMass_nonneg _) (hf i) _)
      _ ≤ |P.coeff e| * H ^ D := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [Finset.prod_pow_eq_pow_sum]
        apply pow_le_pow_right₀ hH
        have heD := (MvPolynomial.le_totalDegree he).trans hP
        rw [Finsupp.sum_fintype e (fun _ (v : ℕ) => v) (fun _ => rfl)] at heD
        exact heD
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact (coefficientMass_sum _ _).trans
    ((Finset.sum_le_sum hterm).trans_eq (Finset.sum_mul _ _ _).symm)

noncomputable def exponentBox (n D : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.univ : Finset (Fin n → Fin (D + 1))).image
    (fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)))

theorem support_subset_exponentBox {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) : P.support ⊆ exponentBox n D := by
  classical
  intro e he
  have hd := (MvPolynomial.le_totalDegree he).trans hP
  have hi (i : Fin n) : e i ≤ D :=
    (Finsupp.single_eval_le_sum e (g := id) rfl (fun _ => Nat.zero_le _) i).trans hd
  apply Finset.mem_image.mpr
  refine ⟨(fun i => (⟨e i, Nat.lt_succ_of_le (hi i)⟩ : Fin (D + 1))), Finset.mem_univ _, ?_⟩
  ext i
  simp

theorem exponentBox_card_le (n D : ℕ) : (exponentBox n D).card ≤ (D + 1) ^ n := by
  classical
  exact Finset.card_image_le.trans (by simp [Fintype.card_pi])

/-- Fixed degree and uniform coefficient bounds control the full coefficient
sum by a fixed combinatorial constant. -/
theorem coefficientMass_le_of_coeff_bound {n D : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ D) {H : ℝ} (hH : 0 ≤ H)
    (hcoeff : ∀ e, |P.coeff e| ≤ H) :
    coefficientMass P ≤ ((D + 1) ^ n : ℕ) * H := by
  classical
  rw [coefficientMass_eq_sum _ (exponentBox n D) (support_subset_exponentBox P hP)]
  calc
    _ ≤ ∑ _e ∈ exponentBox n D, H := Finset.sum_le_sum fun e _ => hcoeff e
    _ = ((exponentBox n D).card : ℝ) * H := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast exponentBox_card_le n D) hH

end Submission.Lib.K4ScalarCoreTools.Simulation.CoefficientMass
