import Mathlib
import Submission.Lib.K4CubicTests.PolynomialTaylor
import Submission.Lib.K4QuadraticSheetCore.SheetPolynomials

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# The projected second fundamental form along full-time lines

A line `b : Fin 6 → ℝ` has base point `lineP b σ = (σ, b0 + σ b3, b1 + σ b4)`, base velocity
`lineV b = (1, b3, b4)` and hidden value `lineW b σ = b2 + σ b5`. If the quadratic test
`γ + β w + α w²` and its hidden derivative are bounded by `K` along the line for all
`σ ∈ [0,1]`, then the projected second fundamental form in the line's own direction is
bounded by `200 K³` at every point of the line (`sff_line_bound`). No lower bound on the
hidden derivative and no sheet are used.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial Set

noncomputable section

/-- Base point, base velocity and hidden value of a line. -/
def lineP (b : Fin 6 → ℝ) (σ : ℝ) : Fin 3 → ℝ := ![σ, b 0 + σ * b 3, b 1 + σ * b 4]
def lineV (b : Fin 6 → ℝ) : Fin 3 → ℝ := ![1, b 3, b 4]
def lineW (b : Fin 6 → ℝ) (σ : ℝ) : ℝ := b 2 + σ * b 5

section Taylor

/-- Exact Taylor expansion of a quadratic base polynomial along a line. -/
theorem eval_line_quadratic (γ : BasePoly) (hγ : γ.totalDegree ≤ 2) (P V : Fin 3 → ℝ) (τ : ℝ) :
    eval (fun i => P i + τ * V i) γ =
      eval P γ + τ * dot3 (gradAt γ P) V + τ ^ 2 / 2 * bil3 (hessAt γ P) V V := by
  have hthird : ∀ (i j k : Fin 3), pderiv k (pderiv i (pderiv j γ)) = 0 :=
    pderiv_pderiv_pderiv_eq_zero_of_deg_le_two γ hγ
  have h := Submission.Lib.K4CubicTests.polynomial_line_quadratic_taylor_abs_le γ P
    (fun i => τ * V i) 0 le_rfl (by
      intro t _
      simp only [Submission.Lib.K4CubicTests.polynomialDirectionalDerivative, map_sum,
        Derivation.leibniz, pderiv_C, add_zero, smul_eq_mul, hthird, mul_zero,
        Finset.sum_const_zero, map_mul, eval_C, map_zero, abs_zero]
      exact le_rfl)
  have h0 := abs_nonpos_iff.mp h
  have heq := sub_eq_zero.mp h0
  rw [heq]
  simp only [Submission.Lib.K4CubicTests.polynomialDirectionalDerivative, map_sum,
    Derivation.leibniz, pderiv_C, add_zero, smul_eq_mul, map_mul, eval_C,
    Fin.sum_univ_three, map_add, dot3, bil3, gradAt, hessAt, map_zero, mul_zero, zero_mul]
  ring

/-- Exact Taylor expansion of an affine base polynomial along a line. -/
theorem eval_line_affine (β : BasePoly) (hβ : β.totalDegree ≤ 1) (P V : Fin 3 → ℝ) (τ : ℝ) :
    eval (fun i => P i + τ * V i) β = eval P β + τ * dot3 (gradAt β P) V := by
  have h2 : β.totalDegree ≤ 2 := hβ.trans (by norm_num)
  rw [eval_line_quadratic β h2 P V τ]
  have hz : ∀ i j : Fin 3, pderiv i (pderiv j β) = 0 := fun i j =>
    pderiv_pderiv_eq_zero_of_deg_le_one β hβ j i
  simp only [bil3, hessAt, hz, map_zero]
  ring

theorem lineP_add (b : Fin 6 → ℝ) (σ τ : ℝ) :
    lineP b (σ + τ) = fun i => lineP b σ i + τ * lineV b i := by
  funext i
  fin_cases i <;> simp [lineP, lineV] <;> ring

end Taylor

section LineBound

variable (α : ℝ) (β γ : BasePoly)

/-- The quadratic test along a line. -/
def testVal (b : Fin 6 → ℝ) (σ : ℝ) : ℝ :=
  eval (lineP b σ) γ + eval (lineP b σ) β * lineW b σ + α * lineW b σ ^ 2

/-- Its hidden derivative along a line. -/
def testDer (b : Fin 6 → ℝ) (σ : ℝ) : ℝ := eval (lineP b σ) β + 2 * α * lineW b σ

/-- The discriminant at a line point is `G_w² - 4 α G`. -/
theorem discV_line (b : Fin 6 → ℝ) (σ : ℝ) :
    discV α (eval (lineP b σ) γ) (eval (lineP b σ) β) =
      testDer α β b σ ^ 2 - 4 * α * testVal α β γ b σ := by
  simp only [discV, testDer, testVal]
  ring

/-- A quadratic bounded by `K` on a unit interval containing `0` has bounded coefficients. -/
theorem quadratic_coeff_bounds (A B C K a : ℝ) (ha0 : a ≤ 0) (ha1 : 0 ≤ a + 1)
    (hq : ∀ τ ∈ Icc a (a + 1), |A + B * τ + C * τ ^ 2| ≤ K) :
    |A| ≤ K ∧ |B| ≤ 10 * K ∧ |C| ≤ 8 * K := by
  have h0 := hq 0 ⟨ha0, ha1⟩
  have h1 := hq a ⟨le_rfl, by linarith⟩
  have h2 := hq (a + 1 / 2) ⟨by linarith, by linarith⟩
  have h3 := hq (a + 1) ⟨by linarith, le_rfl⟩
  simp only [mul_zero, add_zero, zero_pow two_ne_zero] at h0
  rw [abs_le] at h0 h1 h2 h3
  -- second difference and centred first difference
  have hC : |C| ≤ 8 * K := by
    have e : C = 2 * ((A + B * a + C * a ^ 2) - 2 * (A + B * (a + 1 / 2) + C * (a + 1 / 2) ^ 2) +
      (A + B * (a + 1) + C * (a + 1) ^ 2)) := by ring
    rw [abs_le]; constructor <;> nlinarith
  have hD : |B + 2 * C * (a + 1 / 2)| ≤ 2 * K := by
    have e : B + 2 * C * (a + 1 / 2) =
      (A + B * (a + 1) + C * (a + 1) ^ 2) - (A + B * a + C * a ^ 2) := by ring
    rw [abs_le]; constructor <;> nlinarith
  refine ⟨abs_le.mpr ⟨h0.1, h0.2⟩, ?_, hC⟩
  have hbd : |2 * C * (a + 1 / 2)| ≤ 8 * K := by
    rw [abs_mul, abs_mul, abs_two]
    have : |a + 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg C, abs_nonneg (a + 1 / 2)]
  calc
    |B| = |(B + 2 * C * (a + 1 / 2)) - 2 * C * (a + 1 / 2)| := by ring_nf
    _ ≤ |B + 2 * C * (a + 1 / 2)| + |2 * C * (a + 1 / 2)| := abs_sub _ _
    _ ≤ 10 * K := by linarith

/-- **Line bound.** If the test and its hidden derivative are bounded by `K` along the whole
line on `[0,1]`, the projected form in the line's own direction is at most `200 K³` at every
point of the line. -/
theorem sff_line_bound (hβ : β.totalDegree ≤ 1) (hγ : γ.totalDegree ≤ 2)
    (b : Fin 6 → ℝ) (K : ℝ) (hK : 0 ≤ K) (hα : |2 * α| ≤ K)
    (hfit : ∀ σ ∈ Icc (0 : ℝ) 1, |testVal α β γ b σ| ≤ K ∧ |testDer α β b σ| ≤ K)
    (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    |sffB α (eval (lineP b σ) γ) (eval (lineP b σ) β) (gradAt γ (lineP b σ))
        (gradAt β (lineP b σ)) (hessAt γ (lineP b σ)) (lineV b) (lineV b)| ≤ 200 * K ^ 3 := by
  set P := lineP b σ with hP
  set V := lineV b
  set w := lineW b σ
  set g := eval P γ
  set bb := eval P β
  set gr := gradAt γ P
  set br := gradAt β P
  set H := hessAt γ P
  have hH : SymH H := hessAt_symm γ P
  -- the line identity
  have hid := sff_line_identity α g bb gr br H V w (b 5) hH
  simp only at hid
  set G0 := g + bb * w + α * w ^ 2
  set G1 := dot3 gr V + dot3 br V * w + bb * b 5 + 2 * α * w * b 5
  set G2 := bil3 H V V + 2 * dot3 br V * b 5 + 2 * α * b 5 ^ 2
  set Gw0 := bb + 2 * α * w
  set Gw1 := dot3 br V + 2 * α * b 5
  -- the test along the line is the quadratic `G0 + G1 τ + G2/2 τ²`
  have hline : ∀ τ : ℝ, testVal α β γ b (σ + τ) = G0 + G1 * τ + G2 / 2 * τ ^ 2 := by
    intro τ
    simp only [testVal, lineP_add, eval_line_quadratic γ hγ, eval_line_affine β hβ]
    simp only [lineW, G0, G1, G2, g, bb, gr, br, H, P, V, w]
    ring
  have hder : ∀ τ : ℝ, testDer α β b (σ + τ) = Gw0 + Gw1 * τ := by
    intro τ
    simp only [testDer, lineP_add, eval_line_affine β hβ]
    simp only [lineW, Gw0, Gw1, bb, br, P, V, w]
    ring
  have hq : ∀ τ ∈ Icc (-σ) (-σ + 1), |G0 + G1 * τ + G2 / 2 * τ ^ 2| ≤ K := by
    intro τ hτ
    rw [← hline τ]
    exact (hfit (σ + τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩).1
  obtain ⟨hG0, hG1, hG2⟩ := quadratic_coeff_bounds G0 G1 (G2 / 2) K (-σ)
    (by linarith [hσ.1]) (by linarith [hσ.2]) hq
  have hG2' : |G2| ≤ 16 * K := by
    have : |G2 / 2| = |G2| / 2 := by rw [abs_div, abs_two]
    linarith
  have hGw0 : |Gw0| ≤ K := by
    have := (hfit σ hσ).2
    rw [show σ = σ + 0 by ring, hder 0] at this
    simpa using this
  have hGw1 : |Gw1| ≤ 2 * K := by
    have h1 := (hfit 1 ⟨by norm_num, le_rfl⟩).2
    have h0 := (hfit 0 ⟨le_rfl, by norm_num⟩).2
    rw [show (1 : ℝ) = σ + (1 - σ) by ring, hder] at h1
    rw [show (0 : ℝ) = σ + (0 - σ) by ring, hder] at h0
    have e : Gw1 = (Gw0 + Gw1 * (1 - σ)) - (Gw0 + Gw1 * (0 - σ)) := by ring
    rw [e]
    exact (abs_sub _ _).trans (by linarith)
  rw [hid]
  have hα' : |α| ≤ K / 2 := by
    have : |2 * α| = 2 * |α| := by rw [abs_mul, abs_two]
    linarith
  have hG0' := abs_nonneg G0
  have hG1' := abs_nonneg G1
  have hG2'' := abs_nonneg G2
  have hGw0' := abs_nonneg Gw0
  have hGw1' := abs_nonneg Gw1
  have hα'' := abs_nonneg α
  calc
    |Gw0 ^ 2 * G2 - 2 * Gw0 * G1 * Gw1 + 2 * α * G1 ^ 2 - 2 * G0 * (2 * α * G2 - Gw1 ^ 2)| ≤
        |Gw0| ^ 2 * |G2| + 2 * |Gw0| * |G1| * |Gw1| + 2 * |α| * |G1| ^ 2 +
          2 * |G0| * (2 * |α| * |G2| + |Gw1| ^ 2) := by
      have e1 : |Gw0 ^ 2 * G2| = |Gw0| ^ 2 * |G2| := by rw [abs_mul, abs_pow]
      have e2 : |2 * Gw0 * G1 * Gw1| = 2 * |Gw0| * |G1| * |Gw1| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two]
      have e3 : |2 * α * G1 ^ 2| = 2 * |α| * |G1| ^ 2 := by
        rw [abs_mul, abs_mul, abs_two, abs_pow]
      have e4 : |2 * G0 * (2 * α * G2 - Gw1 ^ 2)| ≤ 2 * |G0| * (2 * |α| * |G2| + |Gw1| ^ 2) := by
        rw [abs_mul, abs_mul, abs_two]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          |2 * α * G2 - Gw1 ^ 2| ≤ |2 * α * G2| + |Gw1 ^ 2| := abs_sub _ _
          _ = 2 * |α| * |G2| + |Gw1| ^ 2 := by rw [abs_mul, abs_mul, abs_two, abs_pow]
      calc
        _ ≤ |Gw0 ^ 2 * G2 - 2 * Gw0 * G1 * Gw1 + 2 * α * G1 ^ 2| +
            |2 * G0 * (2 * α * G2 - Gw1 ^ 2)| := abs_sub _ _
        _ ≤ (|Gw0 ^ 2 * G2 - 2 * Gw0 * G1 * Gw1| + |2 * α * G1 ^ 2|) +
            |2 * G0 * (2 * α * G2 - Gw1 ^ 2)| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|Gw0 ^ 2 * G2| + |2 * Gw0 * G1 * Gw1|) + |2 * α * G1 ^ 2|) +
            |2 * G0 * (2 * α * G2 - Gw1 ^ 2)| := by gcongr; exact abs_sub _ _
        _ ≤ _ := by rw [e1, e2, e3]; linarith
    _ ≤ K ^ 2 * (16 * K) + 2 * K * (10 * K) * (2 * K) + 2 * (K / 2) * (10 * K) ^ 2 +
          2 * K * (2 * (K / 2) * (16 * K) + (2 * K) ^ 2) := by
      gcongr
    _ = 196 * K ^ 3 := by ring
    _ ≤ 200 * K ^ 3 := by nlinarith [pow_nonneg hK 3]

end LineBound

end

end Submission.Lib.K4QuadraticSheetCore
