-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/CoefficientBounds.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/CoefficientBounds.lean.
import Mathlib

/-! Coefficient bounds for bounded-degree affine substitutions. -/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

noncomputable section

open MvPolynomial

/-- The sum of the absolute values of all coefficients. -/
def coefficientMass {σ : Type*} (P : MvPolynomial σ ℝ) : ℝ :=
  ∑ e ∈ P.support, |P.coeff e|

lemma coefficientMass_nonneg {σ : Type*} (P : MvPolynomial σ ℝ) :
    0 ≤ coefficientMass P := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma coefficientMass_eq_sum {σ : Type*} (P : MvPolynomial σ ℝ)
    (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    coefficientMass P = ∑ e ∈ s, |P.coeff e| := by
  classical
  apply Finset.sum_subset hs
  intro e _ he
  simp only [MvPolynomial.mem_support_iff, not_not] at he
  simp [he]

lemma abs_coeff_le_coefficientMass {σ : Type*} (P : MvPolynomial σ ℝ)
    (e : σ →₀ ℕ) : |P.coeff e| ≤ coefficientMass P := by
  classical
  by_cases he : e ∈ P.support
  · exact Finset.single_le_sum (f := fun m => |P.coeff m|)
      (fun _ _ => abs_nonneg _) he
  · simp only [MvPolynomial.mem_support_iff, not_not] at he
    simpa [he] using coefficientMass_nonneg P

lemma coefficientMass_add_le {σ : Type*} (P Q : MvPolynomial σ ℝ) :
    coefficientMass (P + Q) ≤ coefficientMass P + coefficientMass Q := by
  classical
  let s := P.support ∪ Q.support
  rw [coefficientMass_eq_sum (P + Q) s support_add]
  calc
    ∑ e ∈ s, |(P + Q).coeff e|
        ≤ ∑ e ∈ s, (|P.coeff e| + |Q.coeff e|) := by
      exact Finset.sum_le_sum fun e _ => by simpa using abs_add_le (P.coeff e) (Q.coeff e)
    _ = coefficientMass P + coefficientMass Q := by
      rw [Finset.sum_add_distrib, coefficientMass_eq_sum P s Finset.subset_union_left,
        coefficientMass_eq_sum Q s Finset.subset_union_right]

@[simp] lemma coefficientMass_zero {σ : Type*} :
    coefficientMass (0 : MvPolynomial σ ℝ) = 0 := by simp [coefficientMass]

@[simp] lemma coefficientMass_monomial {σ : Type*} (e : σ →₀ ℕ) (r : ℝ) :
    coefficientMass (monomial e r) = |r| := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  · simp [coefficientMass, support_monomial, hr]

@[simp] lemma coefficientMass_C {σ : Type*} (r : ℝ) :
    coefficientMass (C r : MvPolynomial σ ℝ) = |r| := coefficientMass_monomial 0 r

@[simp] lemma coefficientMass_one {σ : Type*} :
    coefficientMass (1 : MvPolynomial σ ℝ) = 1 := by
  simpa using (coefficientMass_C (σ := σ) 1)

@[simp] lemma coefficientMass_X {σ : Type*} (i : σ) :
    coefficientMass (X i : MvPolynomial σ ℝ) = 1 := by
  simp [X]

lemma coefficientMass_sum_le {σ ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) :
    coefficientMass (∑ i ∈ s, P i) ≤ ∑ i ∈ s, coefficientMass (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (coefficientMass_add_le _ _).trans (add_le_add_right ih _)

lemma coefficientMass_mul_le {σ : Type*} (P Q : MvPolynomial σ ℝ) :
    coefficientMass (P * Q) ≤ coefficientMass P * coefficientMass Q := by
  classical
  calc
    coefficientMass (P * Q) = coefficientMass
        (∑ e ∈ P.support, ∑ f ∈ Q.support, monomial (e + f) (P.coeff e * Q.coeff f)) := by
      congr 1
    _ ≤ ∑ e ∈ P.support, ∑ f ∈ Q.support,
        coefficientMass (monomial (e + f) (P.coeff e * Q.coeff f)) := by
      apply (coefficientMass_sum_le _ _).trans
      exact Finset.sum_le_sum fun e _ => coefficientMass_sum_le _ _
    _ = coefficientMass P * coefficientMass Q := by
      simp only [coefficientMass_monomial, abs_mul]
      rw [coefficientMass, coefficientMass, Finset.sum_mul]
      congr 1
      funext e
      rw [Finset.mul_sum]

lemma coefficientMass_pow_le {σ : Type*} (P : MvPolynomial σ ℝ) (n : ℕ) :
    coefficientMass (P ^ n) ≤ coefficientMass P ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coefficientMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (coefficientMass_nonneg _))

lemma coefficientMass_prod_le {σ ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℝ) :
    coefficientMass (∏ i ∈ s, P i) ≤ ∏ i ∈ s, coefficientMass (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (coefficientMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (coefficientMass_nonneg _))

/-- Bounded substitution coefficients cost only a fixed power of the source degree. -/
theorem coefficientMass_bind_le {σ τ : Type*} (P : MvPolynomial σ ℝ)
    (v : σ → MvPolynomial τ ℝ) {A : ℝ} (hA : 1 ≤ A)
    (hv : ∀ i, coefficientMass (v i) ≤ A) :
    coefficientMass (bind₁ v P) ≤ coefficientMass P * A ^ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply (coefficientMass_sum_le _ _).trans
  calc
    ∑ e ∈ P.support, coefficientMass (bind₁ v (monomial e (P.coeff e)))
        ≤ ∑ e ∈ P.support, |P.coeff e| * A ^ P.totalDegree := by
      apply Finset.sum_le_sum
      intro e he
      rw [bind₁_monomial]
      apply (coefficientMass_mul_le _ _).trans
      rw [coefficientMass_C]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (coefficientMass_prod_le _ _).trans
      calc
        ∏ i ∈ e.support, coefficientMass (v i ^ e i)
            ≤ ∏ i ∈ e.support, A ^ e i := by
          apply Finset.prod_le_prod₀
          · intro i _; exact coefficientMass_nonneg _
          · intro i _
            exact (coefficientMass_pow_le _ _).trans
              (pow_le_pow_left₀ (coefficientMass_nonneg _) (hv i) _)
        _ = A ^ (e.sum fun _ n => n) := by
          simp [Finsupp.sum, Finset.prod_pow_eq_pow_sum]
        _ ≤ A ^ P.totalDegree := pow_le_pow_right₀ hA (le_totalDegree he)
    _ = coefficientMass P * A ^ P.totalDegree := by
      rw [← Finset.sum_mul]
      rfl

/-- A degree bound limits every individual exponent. -/
lemma exponent_le_totalDegree {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (e : Fin n →₀ ℕ) (he : e ∈ P.support) (i : Fin n) : e i ≤ P.totalDegree := by
  apply le_trans _ (le_totalDegree he)
  rw [Finsupp.sum_fintype]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  · simp

/-- Even the coarse coordinate cube gives a uniform bound for support size. -/
theorem support_card_le_of_degree {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) : P.support.card ≤ (d + 1) ^ n := by
  classical
  let f : {e // e ∈ P.support} → (Fin n → Fin (d + 1)) :=
    fun e i => ⟨e.1 i, Nat.lt_succ_of_le ((exponent_le_totalDegree P e.1 e.2 i).trans hP)⟩
  have hf : Function.Injective f := by
    intro e f hef
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg Fin.val (congrFun hef i)
  simpa using Fintype.card_le_of_injective f hf

/-- Coefficient bounds and degree bounds imply a uniform coefficient mass bound. -/
theorem coefficientMass_le_of_degree {n d : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ d) {Z : ℝ} (hZ : 0 ≤ Z) (hc : ∀ e, |P.coeff e| ≤ Z) :
    coefficientMass P ≤ ((d + 1) ^ n : ℕ) * Z := by
  calc
    coefficientMass P ≤ (P.support.card : ℝ) * Z := by
      simpa [coefficientMass] using Finset.sum_le_sum (s := P.support) (fun e _ => hc e)
    _ ≤ ((d + 1) ^ n : ℕ) * Z := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast support_card_le_of_degree P hP) hZ

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
