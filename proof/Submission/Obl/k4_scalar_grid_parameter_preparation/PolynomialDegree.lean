/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PolynomialDegree.lean -/
import Mathlib
import Submission.Obl.k4_scalar_grid_parameter_preparation.FourDirections

/-! Algebraic scalar degree restoration: vanishing third partials characterize quadratics. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open MvPolynomial

private theorem mul_nat_succ_eq_zero {a : ℝ} (n : ℕ)
    (h : a * ((n : ℝ) + 1) = 0) : a = 0 :=
  (mul_eq_zero.mp h).resolve_right (by positivity)

/-- A vanishing third partial kills every coefficient with the corresponding
three coordinate factors. -/
theorem coeff_add_three_eq_zero (p : MvPolynomial (Fin 2) ℝ)
    (i j k : Fin 2) (d : Fin 2 →₀ ℕ)
    (h : pderiv i (pderiv j (pderiv k p)) = 0) :
    p.coeff (d + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1) = 0 := by
  have hc := congrArg (fun q : MvPolynomial (Fin 2) ℝ => q.coeff d) h
  simp only [coeff_pderiv, AddMonoidAlgebra.coeff_zero] at hc
  exact mul_nat_succ_eq_zero _ (mul_nat_succ_eq_zero _ (mul_nat_succ_eq_zero _ hc))

/-- In two variables, four vanishing third partials suffice for total degree at
most two. The two mixed orders are fixed and need no commutation convention. -/
theorem totalDegree_le_two_of_third_partials_eq_zero (p : MvPolynomial (Fin 2) ℝ)
    (h000 : pderiv 0 (pderiv 0 (pderiv 0 p)) = 0)
    (h001 : pderiv 0 (pderiv 0 (pderiv 1 p)) = 0)
    (h011 : pderiv 0 (pderiv 1 (pderiv 1 p)) = 0)
    (h111 : pderiv 1 (pderiv 1 (pderiv 1 p)) = 0) : p.totalDegree ≤ 2 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hsum : d.sum (fun _ n => n) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_succ]
    · simp
  rw [hsum]
  by_contra hlarge
  have hpos : 3 ≤ d 0 + d 1 := by omega
  have hd' : p.coeff d ≠ 0 := mem_support_iff.mp hd
  apply hd'
  by_cases h0 : 3 ≤ d 0
  · let e : Fin 2 →₀ ℕ := Finsupp.single 0 (d 0 - 3) + Finsupp.single 1 (d 1)
    have he : e + Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 0 1 = d := by
      ext i
      fin_cases i <;> simp [e] <;> omega
    simpa only [he] using coeff_add_three_eq_zero p 0 0 0 e h000
  · by_cases h00 : 2 ≤ d 0
    · let e : Fin 2 →₀ ℕ := Finsupp.single 0 (d 0 - 2) + Finsupp.single 1 (d 1 - 1)
      have he : e + Finsupp.single 0 1 + Finsupp.single 0 1 + Finsupp.single 1 1 = d := by
        ext i
        fin_cases i <;> simp [e] <;> omega
      simpa only [he] using coeff_add_three_eq_zero p 0 0 1 e h001
    · by_cases h000' : 1 ≤ d 0
      · let e : Fin 2 →₀ ℕ := Finsupp.single 0 (d 0 - 1) + Finsupp.single 1 (d 1 - 2)
        have he : e + Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 1 1 = d := by
          ext i
          fin_cases i <;> simp [e] <;> omega
        simpa only [he] using coeff_add_three_eq_zero p 0 1 1 e h011
      · let e : Fin 2 →₀ ℕ := Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1 - 3)
        have he : e + Finsupp.single 1 1 + Finsupp.single 1 1 + Finsupp.single 1 1 = d := by
          ext i
          fin_cases i <;> simp [e] <;> omega
        simpa only [he] using coeff_add_three_eq_zero p 1 1 1 e h111

/-- Exponent vector of the monomial `t^a y^b`. -/
def binaryExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[local simp] theorem binaryExponent_zero (a b : ℕ) : binaryExponent a b 0 = a := by
  simp [binaryExponent]

@[local simp] theorem binaryExponent_one (a b : ℕ) : binaryExponent a b 1 = b := by
  simp [binaryExponent]

@[local simp] theorem binaryExponent_sum (a b : ℕ) :
    (binaryExponent a b).sum (fun _ n => n) = a + b := by
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · simp

theorem binaryExponent_injective :
    Function.Injective (fun p : ℕ × ℕ => binaryExponent p.1 p.2) := by
  intro a b h
  apply Prod.ext
  · simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
  · simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h

/-- The bounded rectangular collection of monomials of degree at least three. -/
abbrev HighIndex (M : ℕ) := {b : Fin (M + 1) × Fin (M + 1) // 3 ≤ (b.1 : ℕ) + (b.2 : ℕ)}

noncomputable def highPolynomial (M : ℕ) (a : HighIndex M → ℝ) : MvPolynomial (Fin 2) ℝ :=
  ∑ b, monomial (binaryExponent b.val.1 b.val.2) (a b)

theorem highExponent_injective (M : ℕ) :
    Function.Injective (fun b : HighIndex M => binaryExponent b.val.1 b.val.2) := by
  intro b c h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 0) h)
  · exact Fin.ext (by simpa using congrArg (fun d : Fin 2 →₀ ℕ => d 1) h)

@[local simp] theorem highPolynomial_coeff (M : ℕ) (a : HighIndex M → ℝ) (b : HighIndex M) :
    (highPolynomial M a).coeff (binaryExponent b.val.1 b.val.2) = a b := by
  classical
  simp [highPolynomial, coeff_monomial, (highExponent_injective M).eq_iff]

/-- The cubic-and-higher part has no nonzero vector in the kernel of the
four third partials. -/
theorem highPolynomial_eq_zero_of_third_partials (M : ℕ) (a : HighIndex M → ℝ)
    (h000 : pderiv 0 (pderiv 0 (pderiv 0 (highPolynomial M a))) = 0)
    (h001 : pderiv 0 (pderiv 0 (pderiv 1 (highPolynomial M a))) = 0)
    (h011 : pderiv 0 (pderiv 1 (pderiv 1 (highPolynomial M a))) = 0)
    (h111 : pderiv 1 (pderiv 1 (pderiv 1 (highPolynomial M a))) = 0) : a = 0 := by
  have hdeg := totalDegree_le_two_of_third_partials_eq_zero _ h000 h001 h011 h111
  funext b
  have hzero : (highPolynomial M a).coeff (binaryExponent b.val.1 b.val.2) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change (highPolynomial M a).totalDegree < (binaryExponent b.val.1 b.val.2).sum (fun _ n => n)
    rw [binaryExponent_sum]
    exact lt_of_le_of_lt hdeg (by have h := b.property; omega)
  simpa only [highPolynomial_coeff, Pi.zero_apply] using hzero

/-- The four independent components of a symmetric binary cubic derivative. -/
def thirdPartials (p : MvPolynomial (Fin 2) ℝ) : Fin 4 → MvPolynomial (Fin 2) ℝ :=
  ![pderiv 0 (pderiv 0 (pderiv 0 p)), pderiv 0 (pderiv 0 (pderiv 1 p)),
    pderiv 0 (pderiv 1 (pderiv 1 p)), pderiv 1 (pderiv 1 (pderiv 1 p))]

abbrev UnitBox := Set.Icc (0 : Fin 2 → ℝ) 1

local instance unitBoxCompactSpace : CompactSpace UnitBox :=
  isCompact_iff_compactSpace.mp isCompact_Icc

theorem highPolynomial_add (M : ℕ) (a b : HighIndex M → ℝ) :
    highPolynomial M (a + b) = highPolynomial M a + highPolynomial M b := by
  simp [highPolynomial, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem highPolynomial_smul (M : ℕ) (c : ℝ) (a : HighIndex M → ℝ) :
    highPolynomial M (c • a) = c • highPolynomial M a := by
  simp only [highPolynomial, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact (monomial _).map_smul c (a b)

theorem thirdPartials_add (p q : MvPolynomial (Fin 2) ℝ) :
    thirdPartials (p + q) = thirdPartials p + thirdPartials q := by
  ext i
  fin_cases i <;> simp [thirdPartials, map_add]

theorem thirdPartials_smul (c : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    thirdPartials (c • p) = c • thirdPartials p := by
  ext i
  fin_cases i <;> simp [thirdPartials]

def highThirdMap (M : ℕ) : (HighIndex M → ℝ) →ₗ[ℝ] C(UnitBox, Fin 4 → ℝ) where
  toFun a := ⟨fun x i => eval x.val (thirdPartials (highPolynomial M a) i), by
    apply continuous_pi
    intro i
    exact (continuous_eval _).comp continuous_subtype_val⟩
  map_add' a b := by
    ext x i
    simp only [highPolynomial_add, thirdPartials_add, Pi.add_apply, map_add]
    rfl
  map_smul' c a := by
    ext x i
    simp only [highPolynomial_smul, thirdPartials_smul, Pi.smul_apply]
    simp [Algebra.smul_def]

theorem highThirdMap_injective (M : ℕ) : Function.Injective (highThirdMap M) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hpartial (i : Fin 4) : thirdPartials (highPolynomial M a) i = 0 := by
    apply MvPolynomial.funext_set (fun _ => Set.Icc (0 : ℝ) 1)
      (fun _ => Set.Icc_infinite (by norm_num))
    intro x hx
    have hx' : x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 :=
      ⟨fun i => (hx i (by trivial)).1, fun i => (hx i (by trivial)).2⟩
    have h := congrArg (fun f : C(UnitBox, Fin 4 → ℝ) => f ⟨x, hx'⟩ i) ha
    simpa [highThirdMap] using h
  exact highPolynomial_eq_zero_of_third_partials M a
    (hpartial 0) (hpartial 1) (hpartial 2) (hpartial 3)

/-- On bounded-degree tails, the third partials on the unit box control every
coefficient. The constant depends only on the degree. -/
theorem exists_high_coeff_bound (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (a : HighIndex M → ℝ) (E : ℝ), 0 ≤ E →
    (∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
      ∀ i, |eval x (thirdPartials (highPolynomial M a) i)| ≤ E) →
    ∀ b, |a b| ≤ C * E := by
  obtain ⟨C, hC, hanti⟩ := (highThirdMap M).injective_iff_antilipschitz.mp (highThirdMap_injective M)
  refine ⟨C, hC, ?_⟩
  intro a E hE hbound b
  have hnorm : ‖highThirdMap M a‖ ≤ E := by
    apply (ContinuousMap.norm_le _ hE).mpr
    intro x
    apply (pi_norm_le_iff_of_nonneg hE).mpr
    intro i
    exact hbound x.val x.property i
  exact (norm_le_pi_norm a b).trans
    ((ZeroHomClass.bound_of_antilipschitz (highThirdMap M) hanti a).trans
      (mul_le_mul_of_nonneg_left hnorm C.coe_nonneg))

/-- A tail coefficient outside the finite exponent list is zero. -/
theorem highPolynomial_coeff_eq_zero (M : ℕ) (a : HighIndex M → ℝ) (d : Fin 2 →₀ ℕ)
    (h : ∀ b : HighIndex M, binaryExponent b.val.1 b.val.2 ≠ d) :
    (highPolynomial M a).coeff d = 0 := by
  classical
  simp only [highPolynomial, coeff_sum]
  apply Finset.sum_eq_zero
  intro b hb
  simp [coeff_monomial, h b]

/-- The coefficients of the high part of an arbitrary bivariate polynomial. -/
def highCoefficients (M : ℕ) (p : MvPolynomial (Fin 2) ℝ) (b : HighIndex M) : ℝ :=
  p.coeff (binaryExponent b.val.1 b.val.2)

/-- Remove all listed monomials of degree at least three. -/
def quadraticTruncation (M : ℕ) (p : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  p - highPolynomial M (highCoefficients M p)

theorem totalDegree_quadraticTruncation (M : ℕ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ M) : (quadraticTruncation M p).totalDegree ≤ 2 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hsum : d.sum (fun _ n => n) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype]
    · simp [Fin.sum_univ_two]
    · simp
  by_contra hlarge
  have hlarge' : 3 ≤ d 0 + d 1 := by omega
  have hd' : (quadraticTruncation M p).coeff d ≠ 0 := mem_support_iff.mp hd
  apply hd'
  simp only [quadraticTruncation, coeff_sub]
  apply sub_eq_zero.mpr
  by_cases hbounds : d 0 ≤ M ∧ d 1 ≤ M
  · let b : HighIndex M := ⟨(⟨d 0, by omega⟩, ⟨d 1, by omega⟩), hlarge'⟩
    have he : binaryExponent b.val.1 b.val.2 = d := by
      ext i
      fin_cases i <;> simp [b]
    rw [← he, highPolynomial_coeff]
    rfl
  · have hcoeff : p.coeff d = 0 := by
      by_contra hn
      have hle := (le_totalDegree (mem_support_iff.mpr hn)).trans hp
      omega
    rw [hcoeff]
    symm
    apply highPolynomial_coeff_eq_zero
    intro b hb
    have h0 : (b.val.1 : ℕ) = d 0 := by
      simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 0) hb
    have h1 : (b.val.2 : ℕ) = d 1 := by
      simpa using congrArg (fun e : Fin 2 →₀ ℕ => e 1) hb
    have hb0 := b.val.1.isLt
    have hb1 := b.val.2.isLt
    omega

/-- Truncation retains exactly the constant, linear and quadratic coefficients. -/
theorem quadraticTruncation_coeff (M : ℕ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ M) (d : Fin 2 →₀ ℕ) :
    (quadraticTruncation M p).coeff d = if d.sum (fun _ n => n) ≤ 2 then p.coeff d else 0 := by
  classical
  by_cases hd : d.sum (fun _ n => n) ≤ 2
  · rw [ite_eq_left hd]
    have hzero : (highPolynomial M (highCoefficients M p)).coeff d = 0 := by
      apply highPolynomial_coeff_eq_zero
      intro b hb
      have hsum := congrArg (fun e : Fin 2 →₀ ℕ => e.sum (fun _ n => n)) hb
      rw [binaryExponent_sum] at hsum
      have hh := b.property
      omega
    simp only [quadraticTruncation, coeff_sub, hzero, sub_zero]
  · rw [ite_eq_right hd]
    apply coeff_eq_zero_of_totalDegree_lt
    change (quadraticTruncation M p).totalDegree < d.sum (fun _ n => n)
    exact lt_of_le_of_lt (totalDegree_quadraticTruncation M p hp) (by omega)

theorem quadraticTruncation_coeff_le (M : ℕ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ M) (d : Fin 2 →₀ ℕ) :
    |(quadraticTruncation M p).coeff d| ≤ |p.coeff d| := by
  rw [quadraticTruncation_coeff M p hp d]
  split_ifs <;> simp

/-- Every third partial of a quadratic vanishes. -/
theorem third_partial_eq_zero_of_totalDegree_le_two (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ 2) (i j k : Fin 2) :
    pderiv i (pderiv j (pderiv k p)) = 0 := by
  classical
  ext d
  simp only [coeff_pderiv, AddMonoidAlgebra.coeff_zero]
  have hsum : (d + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1).sum
      (fun _ n => n) = d.sum (fun _ n => n) + 3 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  have hc : p.coeff (d + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    change p.totalDegree < (d + Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1).sum (fun _ n => n)
    rw [hsum]
    omega
  simp [hc]

theorem thirdPartials_quadratic_eq_zero (p : MvPolynomial (Fin 2) ℝ) (hp : p.totalDegree ≤ 2) :
    thirdPartials p = 0 := by
  funext i
  fin_cases i
  · exact third_partial_eq_zero_of_totalDegree_le_two p hp 0 0 0
  · exact third_partial_eq_zero_of_totalDegree_le_two p hp 0 0 1
  · exact third_partial_eq_zero_of_totalDegree_le_two p hp 0 1 1
  · exact third_partial_eq_zero_of_totalDegree_le_two p hp 1 1 1

/-- Removing the quadratic terms leaves all four third partials unchanged. -/
theorem thirdPartials_highPolynomial (M : ℕ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.totalDegree ≤ M) :
    thirdPartials (highPolynomial M (highCoefficients M p)) = thirdPartials p := by
  have h := thirdPartials_quadratic_eq_zero _ (totalDegree_quadraticTruncation M p hp)
  have he : p = quadraticTruncation M p + highPolynomial M (highCoefficients M p) := by
    simp [quadraticTruncation]
  conv_rhs => rw [he, thirdPartials_add, h, zero_add]

/-- Each monomial has absolute value at most one on the unit box. -/
theorem abs_eval_binaryMonomial_le (x : Fin 2 → ℝ) (hx : x ∈ Set.Icc (0 : Fin 2 → ℝ) 1)
    (a b : ℕ) (c : ℝ) : |eval x (monomial (binaryExponent a b) c)| ≤ |c| := by
  have hx0 : |x 0| ≤ 1 := by rw [abs_of_nonneg (hx.1 0)]; exact hx.2 0
  have hx1 : |x 1| ≤ 1 := by rw [abs_of_nonneg (hx.1 1)]; exact hx.2 1
  have hp0 : |x 0| ^ a ≤ 1 := pow_le_one₀ (abs_nonneg _) hx0
  have hp1 : |x 1| ^ b ≤ 1 := pow_le_one₀ (abs_nonneg _) hx1
  have he : eval x (monomial (binaryExponent a b) c) = c * x 0 ^ a * x 1 ^ b := by
    simp [eval_monomial, binaryExponent, mul_assoc]
  rw [he, abs_mul, abs_mul, abs_pow, abs_pow]
  calc
    |c| * |x 0| ^ a * |x 1| ^ b ≤ |c| * 1 * 1 := by gcongr
    _ = |c| := by ring

/-- A degree-dependent bound for approximating by an actual quadratic from
uniform bounds for the four third partials on the unit box. -/
theorem quadraticTruncation_error_bound (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (E : ℝ), p.totalDegree ≤ M → 0 ≤ E →
    (∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
      ∀ i, |eval x (thirdPartials p i)| ≤ E) →
    ∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
      |eval x p - eval x (quadraticTruncation M p)| ≤ C * E := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_high_coeff_bound M
  refine ⟨((Fintype.card (HighIndex M) : ℝ) + 1) * C, by positivity, ?_⟩
  intro p E hp hE hpartial
  have hcoeff : ∀ b, |highCoefficients M p b| ≤ C * E := by
    apply hbound _ E hE
    intro x hx i
    rw [thirdPartials_highPolynomial M p hp]
    exact hpartial x hx i
  intro x hx
  have he : eval x p - eval x (quadraticTruncation M p) =
      eval x (highPolynomial M (highCoefficients M p)) := by
    simp [quadraticTruncation]
  rw [he]
  calc
    |eval x (highPolynomial M (highCoefficients M p))| =
        |∑ b : HighIndex M, eval x (monomial (binaryExponent b.val.1 b.val.2) (highCoefficients M p b))| := by
      simp [highPolynomial]
    _ ≤ ∑ b : HighIndex M, |eval x (monomial (binaryExponent b.val.1 b.val.2) (highCoefficients M p b))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : HighIndex M, C * E := by
      apply Finset.sum_le_sum
      intro b hb
      exact (abs_eval_binaryMonomial_le x hx _ _ _).trans (hcoeff b)
    _ = (Fintype.card (HighIndex M) : ℝ) * (C * E) := by simp
    _ ≤ ((Fintype.card (HighIndex M) : ℝ) + 1) * C * E := by
      nlinarith [mul_nonneg hC.le hE]

/-- Uniformly small third partials yield an actual quadratic approximant. -/
theorem exists_quadratic_approximation (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (E : ℝ), p.totalDegree ≤ M → 0 ≤ E →
    (∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
      ∀ i, |eval x (thirdPartials p i)| ≤ E) →
    ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 2 ∧
      ∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
        |eval x p - eval x q| ≤ C * E := by
  obtain ⟨C, hC, hbound⟩ := quadraticTruncation_error_bound M
  exact ⟨C, hC, fun p E hp hE hpartial =>
    ⟨quadraticTruncation M p, totalDegree_quadraticTruncation M p hp, hbound p E hp hE hpartial⟩⟩

/-- The cubic test for the direction `(1,v)`. -/
def cubicTest (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) (v : ℝ) : ℝ :=
  ∑ j : Fin 4, ((3 : ℕ).choose (j : ℕ) : ℝ) * eval x (thirdPartials p j) * v ^ (j : ℕ)

theorem thirdPartials_le_of_four_tests (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ)
    (v : Fin 4 → ℝ) {K E : ℝ} (hK : 1 ≤ K) (hE : 0 ≤ E)
    (hv : ∀ i, |v i| ≤ K) (hsep : ∀ i j, i ≠ j → K⁻¹ ≤ |v i - v j|)
    (htest : ∀ i, |cubicTest p x (v i)| ≤ E) :
    ∀ j, |eval x (thirdPartials p j)| ≤ 96 * K ^ 18 * E := by
  let a : Fin 4 → ℝ := fun j => ((3 : ℕ).choose (j : ℕ) : ℝ) * eval x (thirdPartials p j)
  have ha := cubic_coefficients_le v a hK hE hv hsep htest
  intro j
  have hc : (1 : ℝ) ≤ ((3 : ℕ).choose (j : ℕ) : ℝ) := by fin_cases j <;> norm_num
  have hh : |eval x (thirdPartials p j)| ≤ |a j| := by
    dsimp [a]
    rw [abs_mul, abs_of_nonneg (le_trans zero_le_one hc)]
    exact le_mul_of_one_le_left (abs_nonneg _) hc
  exact hh.trans (ha j)

/-- Quantitative scalar degree restoration from four separated direction
tests. The constant depends only on the original degree bound. -/
theorem quadratic_restoration_of_four_directions (M : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (v : Fin 4 → ℝ) (K E : ℝ),
      p.totalDegree ≤ M → 1 ≤ K → 0 ≤ E → (∀ i, |v i| ≤ K) →
      (∀ i j, i ≠ j → K⁻¹ ≤ |v i - v j|) →
      (∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
        ∀ i, |cubicTest p x (v i)| ≤ E) →
      ∃ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ 2 ∧
        ∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
          |eval x p - eval x q| ≤ C * K ^ 18 * E := by
  obtain ⟨C, hC, hrest⟩ := exists_quadratic_approximation M
  refine ⟨96 * C, by positivity, ?_⟩
  intro p v K E hp hK hE hv hsep htest
  have hthird : ∀ x : Fin 2 → ℝ, x ∈ Set.Icc (0 : Fin 2 → ℝ) 1 →
      ∀ j, |eval x (thirdPartials p j)| ≤ 96 * K ^ 18 * E := by
    intro x hx
    exact thirdPartials_le_of_four_tests p x v hK hE hv hsep (htest x hx)
  obtain ⟨q, hq, herr⟩ := hrest p _ hp (by positivity) hthird
  refine ⟨q, hq, ?_⟩
  intro x hx
  exact (herr x hx).trans_eq (by ring)

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
