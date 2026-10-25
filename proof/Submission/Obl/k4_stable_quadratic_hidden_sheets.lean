import Mathlib
import ChallengeDeps
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Variation
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet
set_option linter.unusedVariables false

/-!
# `Submission.k4_stable_quadratic_hidden_sheets`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_stable_quadratic_hidden_sheets`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_stable_quadratic_hidden_sheets/`
belong to this obligation.

Proof, with `C = 20` and `r = A ^ (-20)`: the discriminant `D = b ^ 2 - 4 a c` has
`D(u₀) = σ ^ 2 - 4 a Q(u₀, w₀) ≥ 3 / (4 A ^ 2)` with `σ = 2 a w₀ + b(u₀)`, and its coefficient
bound moves it by at most `1 / (4 A ^ 2)` on the complex `r`-ball (`eval₂_sub_le`), so
`Re D > 0` there. The branch is `(-b + s √D) / (2 a)` (`s` the sign of `σ`) when `a ≠ 0` and
`-c / b` when `a = 0` (`exists_sheet`); `real_branch_bounds` gives the real bounds and the
fitting estimate.
-/

namespace Submission.Obl.k4_stable_quadratic_hidden_sheets

open MvPolynomial

theorem num_ball (A : ℝ) (hA : 2 ≤ A) : 216 * A * A ^ 2 * (A ^ 20)⁻¹ ≤ 1 / (4 * A ^ 2) := by
  have hA0 : 0 < A := by linarith
  have h15 : (864 : ℝ) ≤ A ^ 15 :=
    calc (864 : ℝ) ≤ 2 ^ 15 := by norm_num
      _ ≤ A ^ 15 := pow_le_pow_left₀ (by norm_num) hA 15
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 : 0 < A ^ 5 := by positivity
  have : A ^ 20 = A ^ 5 * A ^ 15 := by ring
  rw [this]
  nlinarith

theorem num_disc0 (A : ℝ) (hA : 2 ≤ A) : 4 * ((A ^ 20)⁻¹ * A) ≤ 1 / (4 * A ^ 2) := by
  have hA0 : 0 < A := by linarith
  have h17 : (16 : ℝ) ≤ A ^ 17 :=
    calc (16 : ℝ) ≤ 2 ^ 17 := by norm_num
      _ ≤ A ^ 17 := pow_le_pow_left₀ (by norm_num) hA 17
  have e : 4 * ((A ^ 20)⁻¹ * A) = 4 * A / A ^ 20 := by rw [div_eq_mul_inv]; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : 0 < A ^ 3 := by positivity
  have : A ^ 20 = A ^ 3 * A ^ 17 := by ring
  rw [this]
  nlinarith

end Submission.Obl.k4_stable_quadratic_hidden_sheets

open MvPolynomial Submission.Obl.k4_stable_quadratic_hidden_sheets in
theorem Submission.k4_stable_quadratic_hidden_sheets : ∃ C : ℕ, 20 ≤ C ∧ ∀ (A a_fit a : ℝ), 2 ≤ A → 0 < a_fit → ∀ (b c : MvPolynomial (Fin 3) ℝ), b.totalDegree ≤ 1 → c.totalDegree ≤ 2 → (∀ e, |(b * b - MvPolynomial.C (4 * a) * c).coeff e| ≤ A) → |a| * a_fit ≤ A ^ (-20 : ℝ) → ∀ (u₀ : EuclideanSpace ℝ (Fin 3)) (w₀ : ℝ), ‖u₀‖ ≤ A → |a * w₀ ^ 2 + MvPolynomial.eval (fun j => u₀ j) b * w₀ + MvPolynomial.eval (fun j => u₀ j) c| ≤ a_fit * A → A ^ (-1 : ℝ) ≤ |2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b| → |2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b| ≤ A → ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ, DifferentiableOn ℂ f (Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) (A ^ (-(C : ℝ)))) ∧ (∀ z ∈ Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) (A ^ (-(C : ℝ))), (a : ℂ) * (f z) ^ 2 + MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j => z j) b * f z + MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun j => z j) c = 0) ∧ (∀ u : EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < A ^ (-(C : ℝ)) → (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).im = 0 ∧ A ^ (-(C : ℝ)) ≤ |2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b| ∧ |2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b| ≤ A ^ (C : ℝ) ∧ 0 < (2 * a * (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re + MvPolynomial.eval (fun j => u j) b) * (2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b)) ∧ (∀ (u : EuclideanSpace ℝ (Fin 3)) (w : ℝ), ‖u - u₀‖ < A ^ (-(C : ℝ)) → |a * w ^ 2 + MvPolynomial.eval (fun j => u j) b * w + MvPolynomial.eval (fun j => u j) c| ≤ a_fit * A → 0 < (2 * a * w + MvPolynomial.eval (fun j => u j) b) * (2 * a * w₀ + MvPolynomial.eval (fun j => u₀ j) b) → |w - (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).re| ≤ a_fit * A ^ (C : ℝ)) := by
  refine ⟨20, le_rfl, ?_⟩
  intro A a_fit a hA ha_fit b c hb hc hDcoef ha u₀ w₀ hu₀ hQ₀ hσlo hσhi
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hr : A ^ (-((20 : ℕ) : ℝ)) = (A ^ 20)⁻¹ := by
    rw [Real.rpow_neg hA0.le, Real.rpow_natCast]
  have hR : A ^ ((20 : ℕ) : ℝ) = A ^ 20 := Real.rpow_natCast A 20
  rw [hr, hR]
  have ha' : |a| * a_fit ≤ (A ^ 20)⁻¹ := by
    have : A ^ (-20 : ℝ) = (A ^ 20)⁻¹ := by
      rw [show (-20 : ℝ) = -((20 : ℕ) : ℝ) by norm_num]; exact hr
    rwa [this] at ha
  rw [Real.rpow_neg_one] at hσlo
  set σ := 2 * a * w₀ + eval (fun j => u₀ j) b with hσ
  set D := b * b - C (4 * a) * c with hDdef
  set r := (A ^ 20)⁻¹ with hrdef
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hA1)
  have hσne : σ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hσlo
    exact absurd hσlo (not_le.2 (inv_pos.2 hA0))
  -- the discriminant at the centre
  have hD0 : eval (fun j => u₀ j) D = σ ^ 2 - 4 * a *
      (a * w₀ ^ 2 + eval (fun j => u₀ j) b * w₀ + eval (fun j => u₀ j) c) := by
    rw [hDdef, eval_disc, hσ]; ring
  have hcorr : |4 * a * (a * w₀ ^ 2 + eval (fun j => u₀ j) b * w₀ + eval (fun j => u₀ j) c)|
      ≤ 1 / (4 * A ^ 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    refine le_trans ?_ (num_disc0 A hA)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc |a| * |a * w₀ ^ 2 + eval (fun j => u₀ j) b * w₀ + eval (fun j => u₀ j) c|
        ≤ |a| * (a_fit * A) := mul_le_mul_of_nonneg_left hQ₀ (abs_nonneg a)
      _ = (|a| * a_fit) * A := by ring
      _ ≤ (A ^ 20)⁻¹ * A := mul_le_mul_of_nonneg_right ha' hA0.le
  have hσsq_lo : 1 / A ^ 2 ≤ σ ^ 2 := by
    rw [← sq_abs σ, one_div, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hσlo 2
  have hσsq_hi : σ ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs σ]
    exact pow_le_pow_left₀ (abs_nonneg σ) hσhi 2
  have hq4 : 1 / (4 * A ^ 2) = (1 / A ^ 2) / 4 := by field_simp
  have hD0lo : 3 / (4 * A ^ 2) ≤ eval (fun j => u₀ j) D := by
    rw [hD0]
    have := (abs_le.1 hcorr).2
    have h3 : 3 / (4 * A ^ 2) = 1 / A ^ 2 - 1 / (4 * A ^ 2) := by field_simp; ring
    linarith
  have hD0hi : eval (fun j => u₀ j) D ≤ A ^ 2 + 1 / (4 * A ^ 2) := by
    rw [hD0]
    have := (abs_le.1 hcorr).1
    linarith
  -- the variation of the discriminant on the ball
  have hDdeg : D.totalDegree ≤ 2 := by
    rw [hDdef]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by omega)
    · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  have hball : ∀ y : Fin 3 → ℂ, (∀ i, ‖y i - (u₀ i : ℂ)‖ < r) →
      ‖eval₂ (algebraMap ℝ ℂ) y D - ((eval (fun j => u₀ j) D : ℝ) : ℂ)‖ ≤ 1 / (4 * A ^ 2) := by
    intro y hy
    have h := eval₂_sub_le D hDdeg A hDcoef A r hA1 hr0.le hr1 (fun j => (u₀ j : ℂ)) y
      (coord_le_of_norm_le u₀ A hu₀) (fun i => (hy i).le)
    rw [eval₂_ofReal] at h
    exact h.trans (num_ball A hA)
  have hDpos : ∀ y : Fin 3 → ℂ, (∀ i, ‖y i - (u₀ i : ℂ)‖ < r) →
      0 < (eval₂ (algebraMap ℝ ℂ) y D).re := by
    intro y hy
    have h1 := hball y hy
    have h2 := Complex.abs_re_le_norm
      (eval₂ (algebraMap ℝ ℂ) y D - ((eval (fun j => u₀ j) D : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    have h3 := (abs_le.1 (h2.trans h1)).1
    have h4 : 0 < 1 / (4 * A ^ 2) := by positivity
    have h5 : 3 / (4 * A ^ 2) = 3 * (1 / (4 * A ^ 2)) := by ring
    linarith
  have hσ0 : a = 0 → 0 < eval (fun j => u₀ j) b * σ := by
    intro ha0
    have : σ = eval (fun j => u₀ j) b := by rw [hσ, ha0]; ring
    rw [← this]
    exact mul_self_pos.2 hσne
  obtain ⟨f, hf1, hf2, hf3⟩ := exists_sheet a b c u₀ σ r hr0 hσne hσ0 hDpos
  -- the discriminant at real points of the ball
  have hDreal : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < r →
      1 / (2 * A ^ 2) ≤ eval (fun j => u j) b * eval (fun j => u j) b
          - 4 * a * eval (fun j => u j) c ∧
        eval (fun j => u j) b * eval (fun j => u j) b - 4 * a * eval (fun j => u j) c
          ≤ A ^ 2 + 1 := by
    intro u hu
    have h1 := hball (fun j => (u j : ℂ)) (coord_lt_of_norm_sub_lt u₀ u r hu)
    rw [eval₂_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      hDdef, eval_disc] at h1
    rw [← hDdef] at h1
    have h2 := abs_le.1 h1
    have h5 : 1 / (2 * A ^ 2) = 3 / (4 * A ^ 2) - 1 / (4 * A ^ 2) := by field_simp; ring
    have h6 : 1 / (4 * A ^ 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    constructor <;> linarith
  refine ⟨f, hf1, hf2, ?_, ?_⟩
  · intro u hu
    obtain ⟨φ, hφ, hroot, hsign⟩ := hf3 u hu
    obtain ⟨hlo, hhi⟩ := hDreal u hu
    obtain ⟨h1, h2, -⟩ := real_branch_bounds A a_fit a _ _ φ σ hA ha_fit hroot hsign hlo hhi
    rw [hφ, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨rfl, h1, h2, hsign⟩
  · intro u w hu hw hpw
    obtain ⟨φ, hφ, hroot, hsign⟩ := hf3 u hu
    obtain ⟨hlo, hhi⟩ := hDreal u hu
    obtain ⟨-, -, h3⟩ := real_branch_bounds A a_fit a _ _ φ σ hA ha_fit hroot hsign hlo hhi
    rw [hφ, Complex.ofReal_re]
    exact h3 w hw hpw
