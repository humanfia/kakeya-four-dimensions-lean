/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.FinitePolynomialBounds

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- The radial primitive of a homogeneous polynomial field. -/
noncomputable def radialHomogeneousPotential {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (n : ℕ) : MvPolynomial ι ℝ :=
  C (((n : ℝ) + 1)⁻¹) * ∑ i, X i * T i

theorem radialHomogeneousPotential_isHomogeneous {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (n : ℕ) (hT : ∀ i, (T i).IsHomogeneous n) :
    (radialHomogeneousPotential T n).IsHomogeneous (n + 1) := by
  have h : (∑ i, X i * T i).IsHomogeneous (n + 1) :=
    IsHomogeneous.sum _ _ _ fun i _ => by simpa [add_comm] using (isHomogeneous_X ℝ i).mul (hT i)
  exact h.C_mul _

private theorem pderiv_radial_sum {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (j : ι) :
    pderiv j (∑ i, X i * T i) = T j + ∑ i, X i * pderiv j (T i) := by
  classical
  simp only [map_sum, pderiv_mul, pderiv_X, Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply, eq_comm, ite_mul, Finset.sum_ite_eq']

/-- The error in the radial primitive's gradient is a radial primitive
of the skew derivative; this formula contains no degree loss. -/
theorem radialHomogeneousPotential_gradient_error {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (n : ℕ) (hT : ∀ i, (T i).IsHomogeneous n) (j : ι) :
    pderiv j (radialHomogeneousPotential T n) - T j =
      C (((n : ℝ) + 1)⁻¹) * ∑ i, X i * (pderiv j (T i) - pderiv i (T j)) := by
  have hE := (hT j).sum_X_mul_pderiv
  rw [nsmul_eq_mul, ← map_natCast (C : ℝ →+* MvPolynomial ι ℝ) n] at hE
  have hC : C (((n : ℝ) + 1)⁻¹) * C ((n : ℝ) + 1) = (1 : MvPolynomial ι ℝ) := by
    rw [← map_mul, inv_mul_cancel₀ (by positivity : (n : ℝ) + 1 ≠ 0), map_one]
  unfold radialHomogeneousPotential
  rw [pderiv_C_mul, pderiv_radial_sum]
  calc
    _ = C (((n : ℝ) + 1)⁻¹) * (T j + ∑ i, X i * pderiv j (T i)) -
        (C (((n : ℝ) + 1)⁻¹) * C ((n : ℝ) + 1)) * T j := by rw [hC, one_mul]
    _ = C (((n : ℝ) + 1)⁻¹) * ((∑ i, X i * pderiv j (T i)) - C (n : ℝ) * T j) := by
      rw [map_add, map_one]
      ring
    _ = _ := by rw [← hE]; simp only [mul_sub, Finset.sum_sub_distrib]

private theorem coeff_X_mul_bound {ι : Type*} (F : MvPolynomial ι ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hF : ∀ m, |F.coeff m| ≤ M) (i : ι) (m : ι →₀ ℕ) :
    |(X i * F).coeff m| ≤ M := by
  classical
  rw [coeff_X_mul']
  split_ifs
  · exact hF _
  · simpa using hM

/-- Uniform coefficient control of the skew derivative gives uniform
coefficient control of the gradient error, independent of homogeneous degree. -/
theorem radialHomogeneousPotential_coeff_error_le {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (n : ℕ) (hT : ∀ i, (T i).IsHomogeneous n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hskew : ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ ε)
    (j : ι) (m : ι →₀ ℕ) :
    |(pderiv j (radialHomogeneousPotential T n) - T j).coeff m| ≤ (Fintype.card ι : ℝ) * ε := by
  classical
  rw [radialHomogeneousPotential_gradient_error T n hT, coeff_C_mul, abs_mul]
  have hα : |((n : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)
  have hs : |(∑ i, X i * (pderiv j (T i) - pderiv i (T j))).coeff m| ≤ (Fintype.card ι : ℝ) * ε := by
    simp only [coeff_sum]
    calc
      |∑ i : ι, (X i * (pderiv j (T i) - pderiv i (T j))).coeff m| ≤
          ∑ i : ι, |(X i * (pderiv j (T i) - pderiv i (T j))).coeff m| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, ε := Finset.sum_le_sum fun i _ => coeff_X_mul_bound _ ε hε (hskew i j) i m
      _ = _ := by simp
  simpa only [one_mul] using mul_le_mul hα hs (abs_nonneg _) (by positivity)

/-- Differentiation shifts the homogeneous component by one degree. -/
theorem pderiv_homogeneousComponent_succ {ι : Type*}
    (F : MvPolynomial ι ℝ) (n : ℕ) (i : ι) :
    pderiv i (homogeneousComponent (n + 1) F) = homogeneousComponent n (pderiv i F) := by
  classical
  ext m
  simp [coeff_pderiv, coeff_homogeneousComponent, map_add, Finsupp.degree_single,
    ite_mul]

/-- A larger degree cutoff gives the same finite homogeneous decomposition. -/
theorem sum_homogeneousComponent_of_degree_le {ι : Type*}
    (F : MvPolynomial ι ℝ) (D : ℕ) (hD : F.totalDegree ≤ D) :
    (∑ n ∈ Finset.range (D + 1), homogeneousComponent n F) = F := by
  classical
  have hsum : (∑ n ∈ Finset.range (F.totalDegree + 1), homogeneousComponent n F) =
      ∑ n ∈ Finset.range (D + 1), homogeneousComponent n F := by
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hD 1))
    intro n hn hnnot
    apply homogeneousComponent_eq_zero
    have hn' : ¬ n < F.totalDegree + 1 := by simpa only [Finset.mem_range] using hnnot
    omega
  exact hsum.symm.trans (sum_homogeneousComponent F)

private theorem skew_homogeneousComponent_coeff_le {ι : Type*}
    (T : ι → MvPolynomial ι ℝ) (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hskew : ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ ε)
    (i j : ι) (m : ι →₀ ℕ) :
    |(pderiv j (homogeneousComponent n (T i)) -
      pderiv i (homogeneousComponent n (T j))).coeff m| ≤ ε := by
  cases n with
  | zero => simpa using hε
  | succ n =>
      rw [pderiv_homogeneousComponent_succ, pderiv_homogeneousComponent_succ,
        ← map_sub (homogeneousComponent n) (pderiv j (T i)) (pderiv i (T j)),
        coeff_homogeneousComponent]
      split_ifs
      · exact hskew i j m
      · simpa using hε

/-- The polynomial form of radial integration, summed over homogeneous
components through a fixed degree bound. -/
noncomputable def polynomialRadialPotential {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) : MvPolynomial ι ℝ :=
  ∑ n ∈ Finset.range (D + 1), radialHomogeneousPotential (fun i => homogeneousComponent n (T i)) n

theorem polynomialRadialPotential_totalDegree_le {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) : (polynomialRadialPotential T D).totalDegree ≤ D + 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro n hn
  have hn' : n ≤ D := by have h := Finset.mem_range.mp hn; omega
  exact ((radialHomogeneousPotential_isHomogeneous _ n
    (fun i => homogeneousComponent_isHomogeneous n (T i))).totalDegree_le).trans
    (Nat.add_le_add_right hn' 1)

/-- Approximate polynomial Poincare lemma with explicit degree and dimension
loss. A small skew derivative suffices; the field need not be exactly closed. -/
theorem polynomialRadialPotential_coeff_error_le {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) (hD : ∀ i, (T i).totalDegree ≤ D)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hskew : ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ ε)
    (j : ι) (m : ι →₀ ℕ) :
    |(pderiv j (polynomialRadialPotential T D) - T j).coeff m| ≤
      (D + 1 : ℕ) * (Fintype.card ι : ℝ) * ε := by
  classical
  have heq : pderiv j (polynomialRadialPotential T D) - T j =
      ∑ n ∈ Finset.range (D + 1),
        (pderiv j (radialHomogeneousPotential (fun i => homogeneousComponent n (T i)) n) -
          homogeneousComponent n (T j)) := by
    calc
      _ = (∑ n ∈ Finset.range (D + 1),
          pderiv j (radialHomogeneousPotential (fun i => homogeneousComponent n (T i)) n)) -
          ∑ n ∈ Finset.range (D + 1), homogeneousComponent n (T j) := by
        rw [sum_homogeneousComponent_of_degree_le (T j) D (hD j)]
        simp only [polynomialRadialPotential, map_sum]
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [heq, coeff_sum]
  calc
    _ ≤ ∑ n ∈ Finset.range (D + 1),
        |(pderiv j (radialHomogeneousPotential (fun i => homogeneousComponent n (T i)) n) -
          homogeneousComponent n (T j)).coeff m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (D + 1), (Fintype.card ι : ℝ) * ε := by
      apply Finset.sum_le_sum
      intro n hn
      exact radialHomogeneousPotential_coeff_error_le _ n
        (fun i => homogeneousComponent_isHomogeneous n (T i)) ε hε
        (skew_homogeneousComponent_coeff_le T n ε hε hskew) j m
    _ = _ := by simp; ring

/-- The exact polynomial Poincare lemma as a consequence of the quantitative
one, retaining the explicit degree bound. -/
theorem exists_polynomial_potential_of_closed_field {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) (hD : ∀ i, (T i).totalDegree ≤ D)
    (hclosed : ∀ i j, pderiv j (T i) = pderiv i (T j)) :
    ∃ P : MvPolynomial ι ℝ, P.totalDegree ≤ D + 1 ∧ ∀ j, pderiv j P = T j := by
  refine ⟨polynomialRadialPotential T D, polynomialRadialPotential_totalDegree_le T D, ?_⟩
  intro j
  apply sub_eq_zero.mp
  ext m
  have h := polynomialRadialPotential_coeff_error_le T D hD 0 le_rfl
    (fun i j m => by simp [hclosed i j]) j m
  have hz : (pderiv j (polynomialRadialPotential T D) - T j).coeff m = 0 :=
    abs_eq_zero.mp (le_antisymm (by simpa using h) (abs_nonneg _))
  simpa using hz

/-- The constructed potential loses precisely one degree before taking
its gradient. -/
theorem polynomialRadialPotential_pderiv_totalDegree_le {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) (j : ι) :
    (pderiv j (polynomialRadialPotential T D)).totalDegree ≤ D := by
  classical
  unfold polynomialRadialPotential
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro n hn
  have hhom : (pderiv j (radialHomogeneousPotential (fun i => homogeneousComponent n (T i)) n)).IsHomogeneous n := by
    simpa using (radialHomogeneousPotential_isHomogeneous _ n
      (fun i => homogeneousComponent_isHomogeneous n (T i))).pderiv
  exact hhom.totalDegree_le.trans (by have hn' := Finset.mem_range.mp hn; omega)

/-- The gradient error has no larger degree than the original field. -/
theorem polynomialRadialPotential_gradient_error_totalDegree_le {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) (hD : ∀ i, (T i).totalDegree ≤ D) (j : ι) :
    (pderiv j (polynomialRadialPotential T D) - T j).totalDegree ≤ D := by
  have hneg : (-T j).totalDegree ≤ D := by
    rw [show -T j = C (-1 : ℝ) * T j by simp]
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hD j)
  rw [sub_eq_add_neg]
  exact (totalDegree_add _ _).trans (max_le (polynomialRadialPotential_pderiv_totalDegree_le T D j) hneg)

/-- Uniform approximate conservativity on a coordinate box, with all degree
and dimension losses displayed explicitly. -/
theorem polynomialRadialPotential_eval_error_le {ι : Type*} [Fintype ι]
    (T : ι → MvPolynomial ι ℝ) (D : ℕ) (hD : ∀ i, (T i).totalDegree ≤ D)
    (ε A : ℝ) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hskew : ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ ε)
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ A) (j : ι) :
    |MvPolynomial.eval x (pderiv j (polynomialRadialPotential T D)) - MvPolynomial.eval x (T j)| ≤
      (D + 1 : ℕ) ^ 2 * (Fintype.card ι : ℝ) * (max 1 ((Fintype.card ι : ℝ) * A)) ^ D * ε := by
  have h := finite_polynomial_eval_abs_le
    (pderiv j (polynomialRadialPotential T D) - T j) D
    (polynomialRadialPotential_gradient_error_totalDegree_le T D hD j)
    A ((D + 1 : ℕ) * (Fintype.card ι : ℝ) * ε) hA (by positivity)
    (polynomialRadialPotential_coeff_error_le T D hD ε hε hskew j) x hx
  calc
    _ = |MvPolynomial.eval x (pderiv j (polynomialRadialPotential T D) - T j)| := by rw [map_sub]
    _ ≤ (D + 1 : ℕ) * (max 1 ((Fintype.card ι : ℝ) * A)) ^ D *
        ((D + 1 : ℕ) * (Fintype.card ι : ℝ) * ε) := h
    _ = _ := by push_cast; ring

end Submission.Lib.K4CubicTests
