import Mathlib
import Submission.Lib.K4ChartLifting.Normalize

/-!
# Earlier tests in normalized earlier coordinates

The earlier coordinates of a graph point `p = (t, y, h)` are
`Φ p = ((t - t₀) / q, D⁻¹ (y - c - t u), B h)`. A raw quadratic test `P` is
carried to the normalized test `normPoly P = P ∘ Φ⁻¹`, the substitution of the
inverse affine map `(τ, ζ, H) ↦ (t₀ + q τ, c + (t₀ + q τ) u + D ζ, B⁻¹ H)`.
The substitution keeps total degree at most two, evaluates at `Φ p` as `P` at
`p`, and divides the hidden derivatives by `B` and `B ^ 2`.

The coordinate maps are passed as functions together with their defining
equations, so that the lemmas apply to the frozen explicit maps as they stand.
-/

namespace Submission.Obl.k4_raw_earlier_witness_normalization

open MvPolynomial
open Submission.Lib.K4ChartLifting

/-- The inverse earlier frame as a polynomial substitution. -/
noncomputable def invSubst (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C t₀ + C q * X 0,
    C (c 0) + (C t₀ + C q * X 0) * C (u 0) + C (D 0 0) * X 1 + C (D 0 1) * X 2,
    C (c 1) + (C t₀ + C q * X 0) * C (u 1) + C (D 1 0) * X 1 + C (D 1 1) * X 2,
    C B⁻¹ * X 3]

/-- A raw earlier test written in normalized earlier coordinates. -/
noncomputable def normPoly (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (invSubst t₀ q B c u D) P

theorem totalDegree_invSubst_le (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) :
    (invSubst t₀ q B c u D i).totalDegree ≤ 1 := by
  have h0 : (C t₀ + C q * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  fin_cases i
  · exact h0
  · exact deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_mul_C _ h0))
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_mul_C _ h0))
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))
  · exact deg1_C_mul _ (deg1_X _)

/-- The substitution does not raise total degree. -/
theorem totalDegree_normPoly_le (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    (normPoly t₀ q B c u D P).totalDegree ≤ P.totalDegree :=
  Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one _
    (totalDegree_invSubst_le t₀ q B c u D) P

theorem pderiv_three_invSubst (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 4) :
    pderiv (3 : Fin 4) (invSubst t₀ q B c u D j) = if j = 3 then C B⁻¹ else 0 := by
  fin_cases j <;> simp [invSubst, pderiv_X]

/-- Chain rule: the hidden derivative of the normalized test is `B⁻¹` times the
normalized hidden derivative. -/
theorem pderiv_three_normPoly (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (normPoly t₀ q B c u D P) =
      normPoly t₀ q B c u D (pderiv (3 : Fin 4) P) * C B⁻¹ := by
  rw [normPoly, Submission.Lib.K4ChartLifting.pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · simp only [pderiv_three_invSubst, ↓reduceIte]
    rfl
  · intro j _ hj
    simp [pderiv_three_invSubst, hj]
  · simp

theorem pderiv_three_three_normPoly (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (D : Matrix (Fin 2) (Fin 2) ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D P)) =
      normPoly t₀ q B c u D (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) * C B⁻¹ * C B⁻¹ := by
  rw [pderiv_three_normPoly, Derivation.leibniz, pderiv_C, smul_zero, zero_add, smul_eq_mul,
    pderiv_three_normPoly]
  ring

section Eval

variable (t₀ q B : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (D : Matrix (Fin 2) (Fin 2) ℝ)

/-- The inverse substitution evaluated at the earlier coordinates of `p` returns `p`. -/
theorem eval_invSubst (hq : q ≠ 0) (hB : B ≠ 0) (hD : D.det ≠ 0)
    (Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ p : EuclideanSpace ℝ (Fin 4), Φ p = WithLp.toLp 2
      ![(p 0 - t₀) / q,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 0,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 1,
        B * p 3])
    (p : EuclideanSpace ℝ (Fin 4)) :
    (fun i => eval (fun j => Φ p j) (invSubst t₀ q B c u D i)) = fun i => p i := by
  set w := Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u) with hw
  have hDw := Frame.toEuclideanLin_mul_inv_apply D (isUnit_iff_ne_zero.mpr hD) (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)
  rw [← hw] at hDw
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hDw
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hDw
  simp [Matrix.toLpLin_apply] at h0 h1
  have hq' : q * ((p 0 - t₀) / q) = p 0 - t₀ := by field_simp
  funext i
  fin_cases i
  · simp [invSubst, hΦ, hq']
  · simp only [invSubst, hΦ, ← hw]
    simp [hq']
    linarith
  · simp only [invSubst, hΦ, ← hw]
    simp [hq']
    linarith
  · simp [invSubst, hΦ]
    field_simp

/-- The normalized test at the earlier coordinates of `p` is the raw test at `p`. -/
theorem eval_normPoly (hq : q ≠ 0) (hB : B ≠ 0) (hD : D.det ≠ 0)
    (Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ p : EuclideanSpace ℝ (Fin 4), Φ p = WithLp.toLp 2
      ![(p 0 - t₀) / q,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 0,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 1,
        B * p 3])
    (P : MvPolynomial (Fin 4) ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    eval (fun i => Φ p i) (normPoly t₀ q B c u D P) = eval (fun i => p i) P := by
  rw [normPoly, eval_bind₁', eval_invSubst t₀ q B c u D hq hB hD Φ hΦ p]

theorem eval_pderiv_three_normPoly (hq : q ≠ 0) (hB : B ≠ 0) (hD : D.det ≠ 0)
    (Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ p : EuclideanSpace ℝ (Fin 4), Φ p = WithLp.toLp 2
      ![(p 0 - t₀) / q,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 0,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 1,
        B * p 3])
    (P : MvPolynomial (Fin 4) ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    eval (fun i => Φ p i) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D P)) =
      eval (fun i => p i) (pderiv (3 : Fin 4) P) * B⁻¹ := by
  rw [pderiv_three_normPoly, eval_mul, eval_C, eval_normPoly t₀ q B c u D hq hB hD Φ hΦ]

theorem eval_pderiv_three_three_normPoly (hq : q ≠ 0) (hB : B ≠ 0) (hD : D.det ≠ 0)
    (Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ p : EuclideanSpace ℝ (Fin 4), Φ p = WithLp.toLp 2
      ![(p 0 - t₀) / q,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 0,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 1,
        B * p 3])
    (P : MvPolynomial (Fin 4) ℝ) (p : EuclideanSpace ℝ (Fin 4)) :
    eval (fun i => Φ p i) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D P))) =
      eval (fun i => p i) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) * B⁻¹ * B⁻¹ := by
  rw [pderiv_three_three_normPoly, eval_mul, eval_mul, eval_C,
    eval_normPoly t₀ q B c u D hq hB hD Φ hΦ]

/-- The raw bounds of an earlier test pair at `p` become the normalized bounds at
the earlier coordinates of `p`: values are unchanged, hidden derivatives are
divided by `B` and `B ^ 2`. The first conjunct is carried along unchanged. -/
theorem normalized_tests (hq : q ≠ 0) (hB : 0 < B) (hD : D.det ≠ 0)
    (Φ : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (hΦ : ∀ p : EuclideanSpace ℝ (Fin 4), Φ p = WithLp.toLp 2
      ![(p 0 - t₀) / q,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 0,
        (Matrix.toEuclideanLin D⁻¹ (WithLp.toLp 2 ![p 1, p 2] - c - (p 0) • u)) 1,
        B * p 3])
    (P S : MvPolynomial (Fin 4) ℝ) (K L : ℝ) (Y : Prop) (p : EuclideanSpace ℝ (Fin 4))
    (h : Y ∧ |eval (fun i => p i) P| ≤ K * L ∧
      B * K⁻¹ ≤ |eval (fun i => p i) (pderiv (3 : Fin 4) P)| ∧
      |eval (fun i => p i) (pderiv (3 : Fin 4) P)| ≤ B * K ∧
      |eval (fun i => p i) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ B ^ 2 * (K / L) ∧
      |eval (fun i => p i) S| ≤ K ∧
      |eval (fun i => p i) (pderiv (3 : Fin 4) S)| ≤ B * K ∧
      |eval (fun i => p i) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) S))| ≤ B ^ 2 * K) :
    Y ∧ |eval (fun i => Φ p i) (normPoly t₀ q B c u D P)| ≤ K * L ∧
      K⁻¹ ≤ |eval (fun i => Φ p i) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D P))| ∧
      |eval (fun i => Φ p i) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D P))| ≤ K ∧
      |eval (fun i => Φ p i)
          (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D P)))| ≤ K / L ∧
      |eval (fun i => Φ p i) (normPoly t₀ q B c u D S)| ≤ K ∧
      |eval (fun i => Φ p i) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D S))| ≤ K ∧
      |eval (fun i => Φ p i)
          (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (normPoly t₀ q B c u D S)))| ≤ K := by
  obtain ⟨hY, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hB0 : B ≠ 0 := hB.ne'
  have hBB : 0 < B * B := mul_pos hB hB
  rw [eval_normPoly t₀ q B c u D hq hB0 hD Φ hΦ, eval_normPoly t₀ q B c u D hq hB0 hD Φ hΦ,
    eval_pderiv_three_normPoly t₀ q B c u D hq hB0 hD Φ hΦ,
    eval_pderiv_three_normPoly t₀ q B c u D hq hB0 hD Φ hΦ,
    eval_pderiv_three_three_normPoly t₀ q B c u D hq hB0 hD Φ hΦ,
    eval_pderiv_three_three_normPoly t₀ q B c u D hq hB0 hD Φ hΦ]
  simp only [abs_mul, abs_inv, abs_of_pos hB, mul_assoc, ← mul_inv]
  refine ⟨hY, h1, ?_, ?_, ?_, h5, ?_, ?_⟩
  · rw [← div_eq_mul_inv, le_div_iff₀ hB, mul_comm]
    exact h2
  · rw [← div_eq_mul_inv, div_le_iff₀ hB, mul_comm]
    exact h3
  · rw [← div_eq_mul_inv, div_le_iff₀ hBB, mul_comm, ← sq]
    exact h4
  · rw [← div_eq_mul_inv, div_le_iff₀ hB, mul_comm]
    exact h6
  · rw [← div_eq_mul_inv, div_le_iff₀ hBB, mul_comm, ← sq]
    exact h7

end Eval

end Submission.Obl.k4_raw_earlier_witness_normalization
