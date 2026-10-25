-- Lane B: cubic directional tests of a potential polynomial from fits along lines, and their transfer.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.QuadraticReplacement
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineTransport
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.DenseJet.Transfer
import Submission.Obl.k4_algebraic_sheet_remez.PolynomialDerivatives

/-!
# Cubic directional tests of a potential polynomial

For a real polynomial `P` in three variables, `Pf P` is its evaluation on the base.

* `cubic_test_of_quadratic_fit`: if `t ↦ Pf P (y + t • v)` is within `ε` of a quadratic on
  `[-1, 1]` and `P` has total degree at most `q`, the cubic directional test
  `D³ (Pf P) y (v, v, v)` is `O_q(ε)`.  Along the line, `Pf P` is the univariate polynomial
  `Broad.restrictLine`, whose cubic coefficient is controlled on `[0, 1]` by
  `Broad.exists_coeff_bound_of_near_quadratic`; the cubic test is six times that coefficient.
* `cubic_norm_le`: with all coefficients at most `M` in absolute value, the first six
  derivatives of `Pf P` are `O_q(M R ^ q)` on the ball of radius `R ≥ 1` (Leibniz rule,
  monomial by monomial).
* `cubic_test_transfer`: the cubic test moves by `O_q(M R ^ q ‖x - y‖ ‖p‖ ^ 3)` between two
  points of that ball (mean value inequality with the fourth derivative bound).
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial
open scoped ContDiff

/-- The evaluation of a real polynomial in three variables on the base. -/
def Pf (P : MvPolynomial (Fin 3) ℝ) : Base → ℝ := fun x => MvPolynomial.eval (fun i => x i) P

lemma Pf_C (a : ℝ) : Pf (C a) = fun _ => a := by
  funext x; simp [Pf]

lemma Pf_add (p r : MvPolynomial (Fin 3) ℝ) : Pf (p + r) = fun x => Pf p x + Pf r x := by
  funext x; simp [Pf]

lemma Pf_mul_X (p : MvPolynomial (Fin 3) ℝ) (i : Fin 3) :
    Pf (p * X i) = fun x => Pf p x * x i := by
  funext x; simp [Pf]

theorem contDiff_Pf (P : MvPolynomial (Fin 3) ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (Pf P) := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [Pf_C]; exact contDiff_const
  | add p r hp hr => rw [Pf_add]; exact hp.add hr
  | mul_X p i hp =>
      rw [Pf_mul_X]
      exact hp.mul (contDiff_piLp_apply (𝕜 := ℝ) 2)

/-- The restriction of `Pf P` to a line is the univariate polynomial `restrictLine`. -/
lemma Pf_line_eq_restrictLine {P : MvPolynomial (Fin 3) ℝ} {q : ℕ} (hq : P.totalDegree ≤ q)
    (y v : Base) (t : ℝ) :
    Pf P (y + t • v) = (Broad.restrictLine P (fun i => y i) (fun i => v i) q).eval t := by
  rw [Broad.eval_restrictLine hq]
  simp only [Pf]
  apply congrArg (fun z => MvPolynomial.eval z P)
  funext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  ring

/-- **Cubic test from a quadratic fit along a line.** -/
theorem cubic_test_of_quadratic_fit (q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ) (y v : Base) (α β γ ε : ℝ), P.totalDegree ≤ q → 0 ≤ ε →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, |Pf P (y + t • v) - (α + β * t + γ * t ^ 2)| ≤ ε) →
      |iteratedFDeriv ℝ 3 (Pf P) y (fun _ => v)| ≤ C * ε := by
  obtain ⟨C₀, hC₀, hcoeff⟩ := Broad.exists_coeff_bound_of_near_quadratic q
  refine ⟨6 * C₀, by positivity, ?_⟩
  intro P y v α β γ ε hq hε hfit
  set f : Polynomial ℝ := Broad.restrictLine P (fun i => y i) (fun i => v i) q
  set g : Polynomial ℝ := Polynomial.C α + Polynomial.C β * Polynomial.X +
    Polynomial.C γ * Polynomial.X ^ 2 with hg
  have hline : ∀ t : ℝ, Pf P (y + t • v) = f.eval t := Pf_line_eq_restrictLine hq y v
  have hgdeg : g.natDegree ≤ 2 := by rw [hg]; compute_degree
  have hgeval : ∀ t, g.eval t = α + β * t + γ * t ^ 2 := by intro t; simp [hg]
  have hclose : ∀ s ∈ Set.Icc (0:ℝ) 1, |f.eval s - g.eval s| ≤ ε := by
    intro s hs
    rw [← hline, hgeval]
    exact hfit s ⟨by linarith [hs.1], hs.2⟩
  have h3 := hcoeff f g 1 ε (Broad.natDegree_restrictLine_le _ _ _ _) hgdeg one_pos hε hclose 3
    le_rfl
  rw [one_pow, div_one] at h3
  have hderiv : iteratedFDeriv ℝ 3 (Pf P) y (fun _ => v) = 6 * f.coeff 3 := by
    rw [← DenseJet.Transfer.iteratedDeriv_line_eq isOpen_univ (contDiff_Pf P).contDiffOn
      (Set.mem_univ y) v 3]
    have hfun : (fun t : ℝ => Pf P (y + t • v)) = fun t => f.eval t := funext hline
    rw [hfun, Submission.Obl.k4_algebraic_sheet_remez.iteratedDeriv_polynomial_eval]
    dsimp only
    rw [Broad.iterate_derivative_eval_zero]
    norm_num [Nat.factorial]
  rw [hderiv, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6), mul_assoc]
  exact mul_le_mul_of_nonneg_left h3 (by norm_num)

/-! ### Derivative bounds from coefficient bounds -/

/-- The derivatives of a coordinate function at a point of norm at most `R ≥ 1`. -/
lemma norm_iteratedFDeriv_coord_le {R : ℝ} (hR : 1 ≤ R) (i : Fin 3) {x : Base} (hx : ‖x‖ ≤ R)
    (j : ℕ) : ‖iteratedFDeriv ℝ j (fun y : Base => y i) x‖ ≤ R := by
  set L : Base →L[ℝ] ℝ := EuclideanSpace.proj i
  have hLx : ∀ y : Base, L y = y i := fun y => rfl
  have hfun : (fun y : Base => y i) = ⇑L := by funext y; rfl
  have hLnorm : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
    rw [hLx, one_mul]
    exact PiLp.norm_apply_le y i
  have hfd : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_zero]
    exact (PiLp.norm_apply_le x i).trans hx
  · rw [← norm_iteratedFDeriv_fderiv, hfun, hfd]
    rcases j with _ | j
    · rw [norm_iteratedFDeriv_zero]; linarith
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp only [Pi.zero_apply, norm_zero]; linarith

/-- The derivatives of a constant. -/
lemma norm_iteratedFDeriv_const_le (a : ℝ) (x : Base) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun _ : Base => a) x‖ ≤ |a| := by
  rcases j with _ | j
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, norm_zero]
    exact abs_nonneg a

/-- Multiplying by a coordinate costs a factor `64 R` in the first six derivatives. -/
lemma norm_iteratedFDeriv_Pf_mul_X_le {R B : ℝ} (hR : 1 ≤ R) (p : MvPolynomial (Fin 3) ℝ)
    (i : Fin 3) {x : Base} (hx : ‖x‖ ≤ R)
    (hB : ∀ j ≤ 6, ‖iteratedFDeriv ℝ j (Pf p) x‖ ≤ B) :
    ∀ j ≤ 6, ‖iteratedFDeriv ℝ j (Pf (p * X i)) x‖ ≤ 64 * R * B := by
  intro j hj
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  rw [Pf_mul_X]
  have hcoord : ContDiff ℝ ⊤ (fun y : Base => y i) := contDiff_piLp_apply (𝕜 := ℝ) 2
  refine (norm_iteratedFDeriv_mul_le (contDiff_Pf p) hcoord x le_top).trans ?_
  calc ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * ‖iteratedFDeriv ℝ l (Pf p) x‖ *
          ‖iteratedFDeriv ℝ (j - l) (fun y : Base => y i) x‖
      ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * B * R := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl' : l ≤ 6 := by rw [Finset.mem_range] at hl; omega
        gcongr
        · exact hB l hl'
        · exact norm_iteratedFDeriv_coord_le hR i hx _
    _ = (2 : ℝ) ^ j * B * R := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 64 * R * B := by
        have h2 : (2 : ℝ) ^ j ≤ 64 := by
          calc (2 : ℝ) ^ j ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hj
            _ = 64 := by norm_num
        have hRB : 0 ≤ B * R := mul_nonneg hB0 (by linarith)
        nlinarith

/-- Multiplying by a power of a coordinate. -/
lemma norm_iteratedFDeriv_Pf_mul_X_pow_le {R B : ℝ} (hR : 1 ≤ R) (p : MvPolynomial (Fin 3) ℝ)
    (i : Fin 3) {x : Base} (hx : ‖x‖ ≤ R)
    (hB : ∀ j ≤ 6, ‖iteratedFDeriv ℝ j (Pf p) x‖ ≤ B) (n : ℕ) :
    ∀ j ≤ 6, ‖iteratedFDeriv ℝ j (Pf (p * X i ^ n)) x‖ ≤ (64 * R) ^ n * B := by
  induction n with
  | zero => simpa using hB
  | succ n ih =>
      intro j hj
      have h := norm_iteratedFDeriv_Pf_mul_X_le hR (p * X i ^ n) i hx ih j hj
      rw [pow_succ, ← mul_assoc]
      calc _ ≤ 64 * R * ((64 * R) ^ n * B) := h
        _ = (64 * R) ^ n * (64 * R) * B := by ring

/-- The first six derivatives of a monomial. -/
lemma norm_iteratedFDeriv_Pf_monomial_le {R : ℝ} (hR : 1 ≤ R) {x : Base} (hx : ‖x‖ ≤ R)
    (s : Fin 3 →₀ ℕ) (a : ℝ) :
    ∀ j ≤ 6, ‖iteratedFDeriv ℝ j (Pf (monomial s a)) x‖ ≤
      |a| * (64 * R) ^ (Finsupp.degree s) := by
  induction s using Finsupp.induction generalizing a with
  | zero =>
      intro j _
      rw [monomial_zero', Pf_C, map_zero, pow_zero, mul_one]
      exact norm_iteratedFDeriv_const_le a x j
  | single_add i b f _ _ ih =>
      have hmono : monomial (Finsupp.single i b + f) a = monomial f a * X i ^ b := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, mul_one, add_comm]
      intro j hj
      rw [hmono]
      refine (norm_iteratedFDeriv_Pf_mul_X_pow_le hR (monomial f a) i hx (ih a) b j hj).trans
        (le_of_eq ?_)
      rw [map_add, Finsupp.degree_single, pow_add]
      ring

/-- The expansion of `Pf P` into its monomials. -/
lemma Pf_eq_sum_monomial (P : MvPolynomial (Fin 3) ℝ) :
    Pf P = fun x => ∑ s ∈ P.support, Pf (monomial s (P.coeff s)) x := by
  funext x
  simp only [Pf]
  conv_lhs => rw [P.as_sum]
  rw [map_sum]

/-- A polynomial in three variables of total degree at most `q` has at most `(q + 1) ^ 3`
monomials. -/
lemma card_support_le_of_totalDegree_le {P : MvPolynomial (Fin 3) ℝ} {q : ℕ}
    (hq : P.totalDegree ≤ q) : P.support.card ≤ (q + 1) ^ 3 := by
  classical
  have hle : ∀ s ∈ P.support, ∀ i, s i ≤ q := by
    intro s hs i
    have h1 : s i ≤ Finsupp.degree s := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ i)
    have h2 : Finsupp.degree s ≤ P.totalDegree := le_totalDegree hs
    omega
  let φ : (Fin 3 →₀ ℕ) → (Fin 3 → Fin (q + 1)) := fun s i => ⟨min (s i) q, by omega⟩
  have hinj : Set.InjOn φ P.support := by
    intro s hs t ht hst
    ext i
    have h := congrFun hst i
    simp only [φ, Fin.mk.injEq] at h
    have hs' := hle s hs i
    have ht' := hle t ht i
    omega
  calc P.support.card ≤ (Finset.univ : Finset (Fin 3 → Fin (q + 1))).card :=
        Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = (q + 1) ^ 3 := by simp

/-- **Derivative norms of a potential polynomial from coefficient bounds.** -/
theorem cubic_norm_le (q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ) (M R : ℝ) (x : Base), P.totalDegree ≤ q → 0 ≤ M → 1 ≤ R →
      (∀ m, |P.coeff m| ≤ M) → ‖x‖ ≤ R →
      ∀ k ≤ 6, ‖iteratedFDeriv ℝ k (Pf P) x‖ ≤ C * M * R ^ q := by
  refine ⟨((q : ℝ) + 1) ^ 3 * 64 ^ q, by positivity, ?_⟩
  intro P M R x hq hM hR hcoeff hx k hk
  have h64 : (1 : ℝ) ≤ 64 * R := by linarith
  have hsum : iteratedFDeriv ℝ k (Pf P) x =
      ∑ s ∈ P.support, iteratedFDeriv ℝ k (Pf (monomial s (P.coeff s))) x := by
    rw [Pf_eq_sum_monomial P, iteratedFDeriv_sum (fun s _ => contDiff_Pf _), Finset.sum_apply]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ s ∈ P.support,
      ‖iteratedFDeriv ℝ k (Pf (monomial s (P.coeff s))) x‖ ≤ M * (64 * R) ^ q := by
    intro s hs
    refine (norm_iteratedFDeriv_Pf_monomial_le hR hx s (P.coeff s) k hk).trans ?_
    have hdeg : Finsupp.degree s ≤ q := (le_totalDegree hs).trans hq
    have hpow : (64 * R) ^ Finsupp.degree s ≤ (64 * R) ^ q := pow_le_pow_right₀ h64 hdeg
    exact mul_le_mul (hcoeff s) hpow (by positivity) hM
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (P.support.card : ℝ) ≤ ((q : ℝ) + 1) ^ 3 := by
    exact_mod_cast card_support_le_of_totalDegree_le hq
  calc (P.support.card : ℝ) * (M * (64 * R) ^ q)
      ≤ ((q : ℝ) + 1) ^ 3 * (M * (64 * R) ^ q) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((q : ℝ) + 1) ^ 3 * 64 ^ q * M * R ^ q := by rw [mul_pow]; ring

/-- **Transfer of a cubic directional test between two base points.** -/
theorem cubic_test_transfer (q : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ) (M R : ℝ) (x y p : Base), P.totalDegree ≤ q → 0 ≤ M →
      1 ≤ R → (∀ m, |P.coeff m| ≤ M) → ‖x‖ ≤ R → ‖y‖ ≤ R →
      |iteratedFDeriv ℝ 3 (Pf P) x (fun _ => p) - iteratedFDeriv ℝ 3 (Pf P) y (fun _ => p)| ≤
        C * M * R ^ q * ‖x - y‖ * ‖p‖ ^ 3 := by
  obtain ⟨C, hC, hnorm⟩ := cubic_norm_le q
  refine ⟨C, hC, ?_⟩
  intro P M R x y p hq hM hR hcoeff hx hy
  have hcd : ContDiff ℝ ∞ (Pf P) := contDiff_Pf P
  have hdiff : ∀ z ∈ Metric.closedBall (0 : Base) R,
      DifferentiableAt ℝ (iteratedFDeriv ℝ 3 (Pf P)) z := fun z _ =>
    (hcd.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top 3))) z
  have hbound : ∀ z ∈ Metric.closedBall (0 : Base) R,
      ‖fderiv ℝ (iteratedFDeriv ℝ 3 (Pf P)) z‖ ≤ C * M * R ^ q := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hnorm P M R z hq hM hR hcoeff (by simpa using hz) (3 + 1) (by norm_num)
  have hmove : ‖iteratedFDeriv ℝ 3 (Pf P) x - iteratedFDeriv ℝ 3 (Pf P) y‖ ≤
      C * M * R ^ q * ‖x - y‖ :=
    (convex_closedBall (0 : Base) R).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (by simpa using hy) (by simpa using hx)
  have hh := (iteratedFDeriv ℝ 3 (Pf P) x - iteratedFDeriv ℝ 3 (Pf P) y).le_opNorm (fun _ => p)
  have heval : |iteratedFDeriv ℝ 3 (Pf P) x (fun _ => p) -
      iteratedFDeriv ℝ 3 (Pf P) y (fun _ => p)| ≤
      ‖iteratedFDeriv ℝ 3 (Pf P) x - iteratedFDeriv ℝ 3 (Pf P) y‖ * ‖p‖ ^ 3 := by
    simpa using hh
  exact heval.trans (mul_le_mul_of_nonneg_right hmove (by positivity))

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
