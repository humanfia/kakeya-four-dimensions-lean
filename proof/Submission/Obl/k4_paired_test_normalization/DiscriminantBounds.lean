-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/DiscriminantBounds.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.Interface
import Submission.Obl.k4_algebraic_real_jet_comparison.HolomorphicBounds

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial Set Metric

private noncomputable def exponentVector (n D : ℕ) (a : Fin n → Fin (D + 1)) : Fin n →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun i => (a i : ℕ)) (fun i _ => Finset.mem_univ i)

/-- A universal finite superset of all supports at one degree bound. -/
noncomputable def monomialSet (n D : ℕ) : Finset (Fin n →₀ ℕ) :=
  Finset.univ.image (exponentVector n D)

theorem support_subset_monomialSet {R : Type*} [CommSemiring R] {n D : ℕ}
    (P : MvPolynomial (Fin n) R)
    (hP : P.totalDegree ≤ D) : P.support ⊆ monomialSet n D := by
  classical
  intro m hm
  have hdeg (i : Fin n) : m i ≤ D :=
    ((monomial_le_degreeOf i hm).trans (degreeOf_le_totalDegree P i)).trans hP
  let a : Fin n → Fin (D + 1) := fun i => ⟨m i, Nat.lt_succ_iff.mpr (hdeg i)⟩
  apply Finset.mem_image.mpr
  refine ⟨a, Finset.mem_univ _, ?_⟩
  ext i
  rfl

/-- Fixed degree and coefficient bounds control values on a fixed complex box. -/
theorem norm_eval_coeff_bound {n D : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : P.totalDegree ≤ D) {A : ℝ} (hA : 0 ≤ A) (hcoeff : ∀ m, ‖P.coeff m‖ ≤ A)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖eval z P‖ ≤ ((monomialSet n D).card : ℝ) * 2 ^ D * A := by
  classical
  have hmon (m) (hm : m ∈ P.support) : ‖eval z (monomial m (P.coeff m))‖ ≤ A * 2 ^ D := by
    rw [eval_monomial, norm_mul]
    apply mul_le_mul (hcoeff m) ?_ (norm_nonneg _) hA
    calc
      ‖m.prod (fun i e => z i ^ e)‖ = ∏ i ∈ m.support, ‖z i‖ ^ m i := by
        simp [Finsupp.prod]
      _ ≤ ∏ i ∈ m.support, (2 : ℝ) ^ m i := by
        exact Finset.prod_le_prod₀ (fun i _ => by positivity)
          (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz i) _)
      _ = (2 : ℝ) ^ m.sum (fun _ e => e) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ (2 : ℝ) ^ D := pow_le_pow_right₀ (by norm_num) ((le_totalDegree hm).trans hP)
  conv_lhs => rw [P.as_sum]
  rw [eval_sum]
  calc
    ‖∑ m ∈ P.support, eval z (monomial m (P.coeff m))‖ ≤
        ∑ m ∈ P.support, ‖eval z (monomial m (P.coeff m))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ P.support, A * 2 ^ D := Finset.sum_le_sum hmon
    _ = (P.support.card : ℝ) * (A * 2 ^ D) := by simp
    _ ≤ ((monomialSet n D).card : ℝ) * (A * 2 ^ D) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card
        (support_subset_monomialSet P hP))) (by positivity)
    _ = ((monomialSet n D).card : ℝ) * 2 ^ D * A := by ring

theorem differentiable_complex_polynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => eval (fun i => z i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
    simp only [eval_add]
    convert hP.add hQ using 1
  | mul_X P j hP =>
    simp only [eval_mul, eval_X]
    convert hP.mul (EuclideanSpace.proj (𝕜 := ℂ) j).differentiable using 1 <;> rfl

/-- The Lipschitz constant depends only on dimension and degree. -/
theorem polynomial_lipschitz_coeff_bound {n D : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : P.totalDegree ≤ D) {A : ℝ} (hA : 0 ≤ A) (hcoeff : ∀ m, ‖P.coeff m‖ ≤ A)
    {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖eval (fun i => y i) P - eval (fun i => x i) P‖ ≤
      (4 * ((monomialSet n D).card : ℝ) * 2 ^ D * A) * ‖y - x‖ := by
  have hbound (z : EuclideanSpace ℂ (Fin n)) (hz : ‖z‖ ≤ 2) :
      ‖eval (fun i => z i) P‖ ≤ ((monomialSet n D).card : ℝ) * 2 ^ D * A :=
    norm_eval_coeff_bound P hP hA hcoeff _ (fun i => (PiLp.norm_apply_le z i).trans hz)
  convert Submission.Obl.k4_algebraic_real_jet_comparison.holomorphic_inner_lipschitz
    (differentiable_complex_polynomial P).differentiableOn hbound hx hy using 1 <;> ring

/-- A small complex oscillation around a positive real discriminant stays in
the right half-plane, where the explicit square-root branches are holomorphic. -/
theorem re_pos_of_discriminant_oscillation {d ρ : ℝ} (hρ : 0 < ρ) (hd : ρ ≤ d)
    {z : ℂ} (hz : ‖z - (d : ℂ)‖ ≤ ρ / 2) : 0 < z.re := by
  have hre := Complex.abs_re_le_norm (z - (d : ℂ))
  have hl := (abs_le.mp (hre.trans hz)).1
  simp only [Complex.sub_re, Complex.ofReal_re] at hl
  linarith

/-- Bounded coefficients and a positive real source value give one quantitative
complex ball on which a discriminant remains in the right half-plane. -/
theorem polynomial_re_pos_ball {n D : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (hP : P.totalDegree ≤ D) {A : ℝ} (hA : 0 ≤ A) (hcoeff : ∀ m, ‖P.coeff m‖ ≤ A)
    {x : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ ≤ (1 : ℝ) / 2)
    {d ρ r : ℝ} (hρ : 0 < ρ) (hd : ρ ≤ d)
    (hvalue : eval (fun i => x i) P = (d : ℂ)) (hr : r ≤ (1 : ℝ) / 2)
    (hsmall : (4 * ((monomialSet n D).card : ℝ) * 2 ^ D * A) * r ≤ ρ / 2) :
    ∀ y ∈ ball x r, 0 < (eval (fun i => y i) P).re := by
  intro y hy
  have hdist : ‖y - x‖ ≤ r := (mem_ball_iff_norm.mp hy).le
  have hy1 : ‖y‖ ≤ 1 := by
    have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
    linarith
  have hx1 : ‖x‖ ≤ 1 := hx.trans (by norm_num)
  have hosc := polynomial_lipschitz_coeff_bound P hP hA hcoeff hx1 hy1
  have hL : 0 ≤ 4 * ((monomialSet n D).card : ℝ) * 2 ^ D * A := by positivity
  have hbound := hosc.trans ((mul_le_mul_of_nonneg_left hdist hL).trans hsmall)
  rw [hvalue] at hbound
  exact re_pos_of_discriminant_oscillation hρ hd hbound

/-- Closed form: the stability constant is uniform over all polynomial coefficients. -/
theorem polynomial_stability_constant (n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : MvPolynomial (Fin n) ℂ), P.totalDegree ≤ D →
      ∀ A : ℝ, 0 ≤ A → (∀ m, ‖P.coeff m‖ ≤ A) →
      ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
      ∀ d ρ r : ℝ, 0 < ρ → ρ ≤ d →
        MvPolynomial.eval (fun i => x i) P = (d : ℂ) →
        0 ≤ r → r ≤ (1 : ℝ) / 2 → C * A * r ≤ ρ / 2 →
        ∀ y ∈ Metric.ball x r, 0 < (MvPolynomial.eval (fun i => y i) P).re := by
  let C₀ : ℝ := 4 * ((monomialSet n D).card : ℝ) * 2 ^ D
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ + 1, by linarith, ?_⟩
  intro P hP A hA hcoeff x hx d ρ r hρ hd hv hr hr' hsmall
  apply polynomial_re_pos_ball P hP hA hcoeff hx hρ hd hv hr'
  calc
    (4 * ((monomialSet n D).card : ℝ) * 2 ^ D * A) * r = C₀ * A * r := rfl
    _ ≤ (C₀ + 1) * A * r := by gcongr; linarith
    _ ≤ ρ / 2 := hsmall

end Submission.Obl.k4_paired_test_normalization
