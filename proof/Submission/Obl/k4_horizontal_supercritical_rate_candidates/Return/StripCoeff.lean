import Submission.Lib.K4ChartLifting.PolyAlgebra
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm

/-!
# Coefficients of a quadratic bounded on a moving strip

A degree-two polynomial in `(t, y)` bounded by `E` on the strip
`{(t, c0 + t c1 + β w) : t ∈ [0,1], w ∈ [-1,1]}` has all coefficients at most
`C E Λ² / β²` when `|c0|, |c1| ≤ Λ`, `Λ ≥ 1` and `0 < β ≤ 1`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MvPolynomial Set
open Submission.Lib.K4ChartLifting

noncomputable section

/-- Strip coordinates `(t, u) ↦ (t, c0 + t c1 + β (2u - 1))`. -/
def stripSubst (c0 c1 β : ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![X 0, C c0 + C c1 * X 0 + C β * (C 2 * X 1 - 1)]

/-- The inverse substitution. -/
def stripInv (c0 c1 β : ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![X 0, C (2 * β)⁻¹ * (X 1 - C c0 - C c1 * X 0) + C (1 / 2)]

theorem stripSubst_degree (c0 c1 β : ℝ) (i : Fin 2) : (stripSubst c0 c1 β i).totalDegree ≤ 1 := by
  fin_cases i
  · change (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1
    simp
  · change (C c0 + C c1 * X (0 : Fin 2) + C β * (C 2 * X 1 - 1) :
      MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
      exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      simp only [totalDegree_C, zero_add]
      refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
      exact (totalDegree_mul _ _).trans (by simp)

theorem eval_stripSubst (c0 c1 β : ℝ) (P : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    eval x (bind₁ (stripSubst c0 c1 β) P) =
      eval ![x 0, c0 + x 0 * c1 + β * (2 * x 1 - 1)] P := by
  have hsub : eval x (bind₁ (stripSubst c0 c1 β) P) =
      eval (fun i => eval x (stripSubst c0 c1 β i)) P := eval₂Hom_bind₁ _ _ _ _
  have hargs : (fun i => eval x (stripSubst c0 c1 β i)) =
      ![x 0, c0 + x 0 * c1 + β * (2 * x 1 - 1)] := by
    funext i
    fin_cases i <;> simp [stripSubst]; ring
  rw [hsub, hargs]

theorem bind_stripInv_stripSubst {c0 c1 β : ℝ} (hβ : β ≠ 0) (P : MvPolynomial (Fin 2) ℝ) :
    bind₁ (stripInv c0 c1 β) (bind₁ (stripSubst c0 c1 β) P) = P := by
  apply MvPolynomial.funext
  intro x
  have h1 : eval x (bind₁ (stripInv c0 c1 β) (bind₁ (stripSubst c0 c1 β) P)) =
      eval (fun i => eval x (stripInv c0 c1 β i)) (bind₁ (stripSubst c0 c1 β) P) :=
    eval₂Hom_bind₁ _ _ _ _
  rw [h1, eval_stripSubst]
  have hargs : (![eval x (stripInv c0 c1 β 0), c0 + eval x (stripInv c0 c1 β 0) * c1 +
      β * (2 * eval x (stripInv c0 c1 β 1) - 1)] : Fin 2 → ℝ) = x := by
    funext i
    fin_cases i
    · simp [stripInv]
    · simp [stripInv]
      field_simp
      ring
  rw [hargs]

theorem coeffL1_stripInv_le {c0 c1 β Λ : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hΛ : 1 ≤ Λ)
    (hc0 : |c0| ≤ Λ) (hc1 : |c1| ≤ Λ) (i : Fin 2) :
    coeffL1 (stripInv c0 c1 β i) ≤ 3 * Λ / β := by
  have hβΛ : 1 ≤ 3 * Λ / β := by rw [le_div_iff₀ hβ]; linarith
  fin_cases i
  · change coeffL1 (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ≤ _
    rw [coeffL1_X]; exact hβΛ
  · change coeffL1 (C (2 * β)⁻¹ * (X 1 - C c0 - C c1 * X (0 : Fin 2)) + C (1 / 2) :
      MvPolynomial (Fin 2) ℝ) ≤ _
    have hin : coeffL1 (X 1 - C c0 - C c1 * X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) ≤
        1 + |c0| + |c1| := by
      refine (coeffL1_sub_le _ _).trans ?_
      refine add_le_add ((coeffL1_sub_le _ _).trans ?_) ?_
      · rw [coeffL1_X, coeffL1_C]
      · refine (coeffL1_C_mul_le _ _).trans ?_
        rw [coeffL1_X, mul_one]
    refine (coeffL1_add_le _ _).trans ?_
    rw [coeffL1_C]
    have h2 : coeffL1 (C (2 * β)⁻¹ * (X 1 - C c0 - C c1 * X (0 : Fin 2)) :
        MvPolynomial (Fin 2) ℝ) ≤ (2 * β)⁻¹ * (1 + 2 * Λ) := by
      refine (coeffL1_C_mul_le _ _).trans ?_
      rw [abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : (2 * β)⁻¹ * (1 + 2 * Λ) + |(1 / 2 : ℝ)| ≤ 3 * Λ / β := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have : (1 / 2 : ℝ) ≤ Λ / (2 * β) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have e : (2 * β)⁻¹ * (1 + 2 * Λ) = (1 + 2 * Λ) / (2 * β) := by rw [inv_mul_eq_div]
      rw [e]
      calc (1 + 2 * Λ) / (2 * β) + 1 / 2 ≤ (1 + 2 * Λ) / (2 * β) + Λ / (2 * β) := by linarith
        _ = (1 + 3 * Λ) / (2 * β) := by ring
        _ ≤ (6 * Λ) / (2 * β) := by
            apply div_le_div_of_nonneg_right _ (by positivity); linarith
        _ = 3 * Λ / β := by field_simp; ring
    linarith

/-- Coefficients of a quadratic bounded on a moving strip. -/
theorem exists_strip_coeff_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ 2 →
      ∀ (c0 c1 β Λ E : ℝ), 0 < β → β ≤ 1 → 1 ≤ Λ → |c0| ≤ Λ → |c1| ≤ Λ → 0 ≤ E →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1, |eval ![t, c0 + t * c1 + β * w] P| ≤ E) →
      ∀ m, |P.coeff m| ≤ C₀ * E * Λ ^ 2 / β ^ 2 := by
  obtain ⟨C₁, hC₁, hR⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_on_unit_cube 2 2
  refine ⟨81 * C₁, by positivity, ?_⟩
  intro P hP c0 c1 β Λ E hβ hβ1 hΛ hc0 hc1 hE hbd m
  set P' := bind₁ (stripSubst c0 c1 β) P with hP'
  have hdeg' : P'.totalDegree ≤ 2 :=
    (totalDegree_bind₁_le_of_le_one _ (stripSubst_degree c0 c1 β) P).trans hP
  have hbd' : ∀ x ∈ Icc (0 : Fin 2 → ℝ) 1, |eval x P'| ≤ E := by
    intro x hx
    rw [hP', eval_stripSubst]
    have hx0 : x 0 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 0, hx.2 0⟩
    have hx1 : x 1 ∈ Icc (0 : ℝ) 1 := ⟨hx.1 1, hx.2 1⟩
    have := hbd (x 0) hx0 (2 * x 1 - 1) ⟨by linarith [hx1.1], by linarith [hx1.2]⟩
    simpa [mul_comm] using this
  have hcoef' : ∀ d, |P'.coeff d| ≤ C₁ * E := hR P' hdeg' E hE hbd'
  have hcard : (P'.support.card : ℝ) ≤ 9 := by
    have := card_support_le (D := 2) P' hdeg'
    exact_mod_cast this
  have hL1' : coeffL1 P' ≤ 9 * (C₁ * E) := by
    unfold coeffL1
    calc ∑ m ∈ P'.support, |P'.coeff m| ≤ ∑ _m ∈ P'.support, C₁ * E :=
          Finset.sum_le_sum (fun m _ => hcoef' m)
      _ = (P'.support.card : ℝ) * (C₁ * E) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 9 * (C₁ * E) := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hS : 1 ≤ 3 * Λ / β := by rw [le_div_iff₀ hβ]; linarith
  have hback := coeffL1_bind₁_le (stripInv c0 c1 β) (3 * Λ / β) hS
    (coeffL1_stripInv_le hβ hβ1 hΛ hc0 hc1) P'
  rw [hP', bind_stripInv_stripSubst hβ.ne'] at hback
  have hpow : (3 * Λ / β) ^ P'.totalDegree ≤ (3 * Λ / β) ^ 2 := pow_le_pow_right₀ hS hdeg'
  calc |P.coeff m| ≤ coeffL1 P := abs_coeff_le_coeffL1 P m
    _ ≤ coeffL1 P' * (3 * Λ / β) ^ P'.totalDegree := hback
    _ ≤ 9 * (C₁ * E) * (3 * Λ / β) ^ 2 :=
        mul_le_mul hL1' hpow (by positivity) (by positivity)
    _ = 81 * C₁ * E * Λ ^ 2 / β ^ 2 := by field_simp; ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
