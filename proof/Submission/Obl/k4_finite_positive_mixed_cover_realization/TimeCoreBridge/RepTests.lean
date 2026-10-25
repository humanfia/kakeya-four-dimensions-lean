-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/RepTests.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/RepTests.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0581, commit 6a8fa645a587,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/RepTests.lean.

import Submission.Lib.K4QuadraticSheets.QuadTest

/-!
# Chart tests from a representative quadratic test

Let `P` be a test of total degree at most two (hidden variable last) and `f` a root of `P` over
the base of a point `x`, with branch derivative normalized by `λ` to lie in `[1/2, 2]`. If the
hidden coordinate of `x` is within `η` of `f`, then

* (`rep_low`) when the curvature is small, `|qc P| η ≤ λ⁻¹/4`, the normalized test `B λ P` has
  value at most `3 B η`, hidden derivative in `[B/4, 9B/4]` and curvature at most `B/(4η)`;
* (`rep_high`) otherwise the affine-centre test `(B / qc P) ∂_w P` has value at most `9 B η`,
  hidden derivative `B` and curvature `0`.

These are the whole-block tests of the improved charts at hidden thickness `≈ B η`.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MvPolynomial Submission.Lib.K4QuadraticSheets

/-- Taylor expansion of a quadratic test in its hidden variable around `f`. -/
theorem eval_quad_expand {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (f w : ℝ) :
    eval (Fin.snoc z w : Fin 4 → ℝ) P = eval (Fin.snoc z f : Fin 4 → ℝ) P +
      eval (Fin.snoc z f : Fin 4 → ℝ) (pderiv (3 : Fin 4) P) * (w - f) +
      qc P / 2 * (w - f) ^ 2 := by
  have h1 := eval_snoc_quadratic (n := 3) P hP z w
  have h2 := eval_snoc_quadratic (n := 3) P hP z f
  have h3 : eval (Fin.snoc z f : Fin 4 → ℝ) (pderiv (3 : Fin 4) P) = qb P z + qc P * f :=
    eval_snoc_pderiv (n := 3) P hP z f
  rw [h1, h2, h3]
  ring

theorem eval_pderiv_expand {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (f w : ℝ) :
    eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (3 : Fin 4) P) =
      eval (Fin.snoc z f : Fin 4 → ℝ) (pderiv (3 : Fin 4) P) + qc P * (w - f) := by
  have h1 : eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (3 : Fin 4) P) = qb P z + qc P * w :=
    eval_snoc_pderiv (n := 3) P hP z w
  have h2 : eval (Fin.snoc z f : Fin 4 → ℝ) (pderiv (3 : Fin 4) P) = qb P z + qc P * f :=
    eval_snoc_pderiv (n := 3) P hP z f
  rw [h1, h2]
  ring

theorem last_three : Fin.last 3 = (3 : Fin 4) := rfl

theorem update_three_eq_snoc (x : Fin 4 → ℝ) (w : ℝ) :
    Function.update x (3 : Fin 4) w = (Fin.snoc (Fin.init x) w : Fin 4 → ℝ) := by
  funext k
  fin_cases k <;> simp [Function.update, Fin.snoc, Fin.init]

theorem snoc_init_eq (x : Fin 4 → ℝ) : (Fin.snoc (Fin.init x) (x 3) : Fin 4 → ℝ) = x := by
  have := Fin.snoc_init_self (α := fun _ => ℝ) x
  simpa using this

/-- Low curvature: the normalized test. -/
theorem rep_low {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {lam η B : ℝ}
    (hlam : 0 < lam) (hB : 0 < B) (hη : 0 < η) (hlow : |qc P| * η ≤ lam⁻¹ / 4)
    {x : Fin 4 → ℝ} {f : ℝ} (hroot : eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) P = 0)
    (hder₁ : 1 / 2 ≤ lam * |eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) (pderiv 3 P)|)
    (hder₂ : lam * |eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) (pderiv 3 P)| ≤ 2)
    (hclose : |x 3 - f| ≤ η) :
    |eval x (C (B * lam) * P)| ≤ 3 * (B * η) ∧
      B / 4 ≤ |eval x (pderiv 3 (C (B * lam) * P))| ∧
      |eval x (pderiv 3 (C (B * lam) * P))| ≤ 9 * B / 4 ∧
      |eval x (pderiv 3 (pderiv 3 (C (B * lam) * P)))| ≤ B / (4 * η) := by
  set z := Fin.init x
  set g := eval (Fin.snoc z f : Fin 4 → ℝ) (pderiv 3 P) with hg
  have hx : x = (Fin.snoc z (x 3) : Fin 4 → ℝ) := (snoc_init_eq x).symm
  have hval : eval x P = g * (x 3 - f) + qc P / 2 * (x 3 - f) ^ 2 := by
    conv_lhs => rw [hx]
    rw [eval_quad_expand hP z f (x 3), hroot, ← hg]
    ring
  have hder : eval x (pderiv 3 P) = g + qc P * (x 3 - f) := by
    conv_lhs => rw [hx]
    rw [eval_pderiv_expand hP z f (x 3)]
  have hcurv : eval x (pderiv 3 (pderiv 3 P)) = qc P :=
    eval_pderiv2_eq_qc (n := 3) P hP x
  have hlamqc : lam * |qc P| * η ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hlow hlam.le
    rw [mul_div_assoc', mul_inv_cancel₀ hlam.ne'] at this
    linarith [mul_assoc lam (|qc P|) η]
  have hd := abs_nonneg (x 3 - f)
  -- the second-order term
  have hsec : lam * |qc P| * |x 3 - f| ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hclose (by positivity)).trans hlamqc
  simp only [map_mul, eval_C, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hval, abs_mul, abs_of_pos (by positivity : 0 < B * lam)]
    have h1 : |g * (x 3 - f) + qc P / 2 * (x 3 - f) ^ 2| ≤ |g| * |x 3 - f| +
        |qc P| / 2 * |x 3 - f| ^ 2 := by
      calc _ ≤ |g * (x 3 - f)| + |qc P / 2 * (x 3 - f) ^ 2| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_div, abs_two, abs_pow]
    have h2 : lam * (|g| * |x 3 - f| + |qc P| / 2 * |x 3 - f| ^ 2) ≤ 2 * η + η / 8 := by
      have e1 : lam * |g| * |x 3 - f| ≤ 2 * η :=
        mul_le_mul hder₂ hclose hd (by norm_num)
      have e2 : lam * |qc P| * |x 3 - f| * |x 3 - f| ≤ 1 / 4 * η :=
        mul_le_mul hsec hclose hd (by norm_num)
      nlinarith
    calc B * lam * |g * (x 3 - f) + qc P / 2 * (x 3 - f) ^ 2|
        ≤ B * lam * (|g| * |x 3 - f| + |qc P| / 2 * |x 3 - f| ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B * (lam * (|g| * |x 3 - f| + |qc P| / 2 * |x 3 - f| ^ 2)) := by ring
      _ ≤ B * (2 * η + η / 8) := mul_le_mul_of_nonneg_left h2 hB.le
      _ ≤ 3 * (B * η) := by nlinarith
  · rw [hder, abs_mul, abs_of_pos (by positivity : 0 < B * lam)]
    have h1 : |g| - |qc P| * |x 3 - f| ≤ |g + qc P * (x 3 - f)| := by
      have := abs_sub_abs_le_abs_sub g (-(qc P * (x 3 - f)))
      rw [abs_neg, abs_mul, sub_neg_eq_add] at this
      exact this
    have h2 : 1 / 4 ≤ lam * (|g| - |qc P| * |x 3 - f|) := by nlinarith
    calc B / 4 = B * (1 / 4) := by ring
      _ ≤ B * (lam * (|g| - |qc P| * |x 3 - f|)) := mul_le_mul_of_nonneg_left h2 hB.le
      _ ≤ B * (lam * |g + qc P * (x 3 - f)|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hlam.le) hB.le
      _ = B * lam * |g + qc P * (x 3 - f)| := by ring
  · rw [hder, abs_mul, abs_of_pos (by positivity : 0 < B * lam)]
    have h1 : |g + qc P * (x 3 - f)| ≤ |g| + |qc P| * |x 3 - f| := by
      calc _ ≤ |g| + |qc P * (x 3 - f)| := abs_add_le _ _
        _ = _ := by rw [abs_mul]
    have h2 : lam * (|g| + |qc P| * |x 3 - f|) ≤ 9 / 4 := by nlinarith
    calc B * lam * |g + qc P * (x 3 - f)| ≤ B * (lam * (|g| + |qc P| * |x 3 - f|)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hlam.le) hB.le
      _ ≤ B * (9 / 4) := mul_le_mul_of_nonneg_left h2 hB.le
      _ = 9 * B / 4 := by ring
  · rw [hcurv, abs_mul, abs_of_pos (by positivity : 0 < B * lam)]
    rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- High curvature: the affine-centre test. -/
theorem rep_high {P : MvPolynomial (Fin 4) ℝ} (hP : P.totalDegree ≤ 2) {lam η B : ℝ}
    (hlam : 0 < lam) (hη : 0 < η) (hB : 0 < B) (hhigh : lam⁻¹ / 4 < |qc P| * η)
    {x : Fin 4 → ℝ} {f : ℝ}
    (hder₂ : lam * |eval (Fin.snoc (Fin.init x) f : Fin 4 → ℝ) (pderiv 3 P)| ≤ 2)
    (hclose : |x 3 - f| ≤ η) :
    |eval x (C (B / qc P) * pderiv 3 P)| ≤ 9 * (B * η) ∧
      eval x (pderiv 3 (C (B / qc P) * pderiv 3 P)) = B ∧
      eval x (pderiv 3 (pderiv 3 (C (B / qc P) * pderiv 3 P))) = 0 := by
  set z := Fin.init x
  set g := eval (Fin.snoc z f : Fin 4 → ℝ) (pderiv 3 P) with hg
  have hx : x = (Fin.snoc z (x 3) : Fin 4 → ℝ) := (snoc_init_eq x).symm
  have hqc0 : qc P ≠ 0 := by
    intro h
    rw [h, abs_zero, zero_mul] at hhigh
    have : 0 < lam⁻¹ / 4 := by positivity
    linarith
  have hder : eval x (pderiv 3 P) = g + qc P * (x 3 - f) := by
    conv_lhs => rw [hx]
    rw [eval_pderiv_expand hP z f (x 3)]
  have hcurv : ∀ y : Fin 4 → ℝ, eval y (pderiv 3 (pderiv 3 P)) = qc P :=
    fun y => eval_pderiv2_eq_qc (n := 3) P hP y
  have h3 : pderiv (3 : Fin 4) (pderiv 3 (pderiv 3 P)) = 0 := by
    have h1 : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 := totalDegree_pderiv_le' P _ hP
    have h0 : (pderiv (3 : Fin 4) (pderiv 3 P)).totalDegree ≤ 0 := totalDegree_pderiv_le' _ _ h1
    rw [eq_C_of_totalDegree_eq_zero _ (Nat.le_zero.mp h0), pderiv_C]
  simp only [map_mul, eval_C, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hder, abs_mul, abs_div]
    -- `|g| ≤ 2 / lam < 8 |qc| η`
    have hg2 : |g| ≤ 2 / lam := by rw [le_div_iff₀ hlam]; linarith
    have hgq : |g| ≤ 8 * (|qc P| * η) := by
      have : 2 / lam = 8 * (lam⁻¹ / 4) := by field_simp; ring
      linarith
    have hqpos : 0 < |qc P| := abs_pos.mpr hqc0
    have h1 : |g + qc P * (x 3 - f)| ≤ |g| + |qc P| * η := by
      calc _ ≤ |g| + |qc P * (x 3 - f)| := abs_add_le _ _
        _ ≤ |g| + |qc P| * η := by
            rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hclose hqpos.le)
    rw [abs_of_pos hB, div_mul_eq_mul_div, div_le_iff₀ hqpos]
    calc B * |g + qc P * (x 3 - f)| ≤ B * (|g| + |qc P| * η) := mul_le_mul_of_nonneg_left h1 hB.le
      _ ≤ B * (9 * (|qc P| * η)) := mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ = 9 * (B * η) * |qc P| := by ring
  · rw [hcurv x]
    field_simp
  · rw [h3, map_zero, mul_zero]

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
