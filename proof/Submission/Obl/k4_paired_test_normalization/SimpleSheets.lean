-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/SimpleSheets.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.Interface
import Mathlib.Analysis.Complex.SqrtDeriv

namespace Submission.Obl.k4_paired_test_normalization

open Set

private lemma complex_sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  simp [Complex.sqrt]

/-- The explicit two branches of a genuinely quadratic equation. -/
noncomputable def quadraticBranch {E : Type*} (a b : E → ℂ) (c σ : ℝ) (z : E) : ℂ :=
  (-b z + (σ : ℂ) * Complex.sqrt (b z ^ 2 - 4 * (c : ℂ) * a z)) / (2 * (c : ℂ))

/-- A discriminant in the right half-plane gives both simple holomorphic branches.
The coefficient functions may be defined on any complex normed space. -/
theorem quadraticBranch_simple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {a b : E → ℂ} {c σ : ℝ} (hc : c ≠ 0) (hσ : σ ^ 2 = 1)
    (ha : DifferentiableOn ℂ a U) (hb : DifferentiableOn ℂ b U)
    (hdisc : ∀ z ∈ U, 0 < (b z ^ 2 - 4 * (c : ℂ) * a z).re) :
    DifferentiableOn ℂ (quadraticBranch a b c σ) U ∧
      ∀ z ∈ U,
        a z + b z * quadraticBranch a b c σ z +
          (c : ℂ) * quadraticBranch a b c σ z ^ 2 = 0 ∧
        b z + 2 * (c : ℂ) * quadraticBranch a b c σ z ≠ 0 := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hd : DifferentiableOn ℂ (fun z => b z ^ 2 - 4 * (c : ℂ) * a z) U :=
    (hb.pow 2).sub (ha.const_mul (4 * (c : ℂ)))
  have hs : DifferentiableOn ℂ
      (fun z => Complex.sqrt (b z ^ 2 - 4 * (c : ℂ) * a z)) U :=
    Complex.differentiableOn_sqrt.comp hd (fun z hz => Or.inl (hdisc z hz))
  refine ⟨?_, ?_⟩
  · change DifferentiableOn ℂ
      (fun z => (-b z + (σ : ℂ) * Complex.sqrt
        (b z ^ 2 - 4 * (c : ℂ) * a z)) * (2 * (c : ℂ))⁻¹) U
    convert (hb.neg.add (hs.const_mul (σ : ℂ))).mul_const (2 * (c : ℂ))⁻¹ using 1
  intro z hz
  have hdne : b z ^ 2 - 4 * (c : ℂ) * a z ≠ 0 := by
    intro heq
    have := hdisc z hz
    simp [heq] at this
  have hsne : Complex.sqrt (b z ^ 2 - 4 * (c : ℂ) * a z) ≠ 0 := by
    intro heq
    have := complex_sqrt_sq (b z ^ 2 - 4 * (c : ℂ) * a z)
    simp [heq] at this
    exact hdne this.symm
  have hσne : (σ : ℂ) ≠ 0 := by
    intro heq
    simp [heq] at hσC
  have hder : b z + 2 * (c : ℂ) * quadraticBranch a b c σ z =
      (σ : ℂ) * Complex.sqrt (b z ^ 2 - 4 * (c : ℂ) * a z) := by
    dsimp [quadraticBranch]
    field_simp [hcC]
    ring
  refine ⟨?_, by rw [hder]; exact mul_ne_zero hσne hsne⟩
  have hid : 4 * (c : ℂ) *
      (a z + b z * quadraticBranch a b c σ z +
        (c : ℂ) * quadraticBranch a b c σ z ^ 2) =
      (b z + 2 * (c : ℂ) * quadraticBranch a b c σ z) ^ 2 -
        (b z ^ 2 - 4 * (c : ℂ) * a z) := by ring
  rw [hder, mul_pow, hσC, one_mul, complex_sqrt_sq, sub_self] at hid
  exact (mul_eq_zero.mp hid).resolve_left (mul_ne_zero (by norm_num) hcC)

/-- On a real input with positive discriminant, either explicit branch is real. -/
theorem quadraticBranch_ofReal {E : Type*} {a b : E → ℂ} {c σ A B : ℝ} {z : E}
    (ha : a z = (A : ℂ)) (hb : b z = (B : ℂ))
    (hd : 0 ≤ B ^ 2 - 4 * c * A) :
    quadraticBranch a b c σ z =
      (((-B + σ * Real.sqrt (B ^ 2 - 4 * c * A)) / (2 * c) : ℝ) : ℂ) := by
  have hreal : b z ^ 2 - 4 * (c : ℂ) * a z = ((B ^ 2 - 4 * c * A : ℝ) : ℂ) := by
    simp [ha, hb]
  have hsqrt : Complex.sqrt (((B ^ 2 - 4 * c * A : ℝ) : ℂ)) =
      (Real.sqrt (B ^ 2 - 4 * c * A) : ℂ) := by
    apply Complex.sqrt_of_nonneg
    exact_mod_cast hd
  unfold quadraticBranch
  rw [hreal, hsqrt, hb]
  simp only [Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- Linear equations give one simple holomorphic sheet without square roots. -/
theorem linearBranch_simple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {a b : E → ℂ} (ha : DifferentiableOn ℂ a U)
    (hb : DifferentiableOn ℂ b U) (hb0 : ∀ z ∈ U, b z ≠ 0) :
    DifferentiableOn ℂ (fun z => -a z / b z) U ∧
      ∀ z ∈ U, a z + b z * (-a z / b z) = 0 ∧ b z ≠ 0 := by
  refine ⟨?_, ?_⟩
  · change DifferentiableOn ℂ (fun z => -a z * (b z)⁻¹) U
    convert ha.neg.mul (hb.inv hb0) using 1
  intro z hz
  refine ⟨?_, hb0 z hz⟩
  field_simp [hb0 z hz]
  ring

/-- Choose the quadratic branch whose derivative has the same sign as the
derivative at the approximate root. The residual controls the root error. -/
theorem quadraticBranch_error {a b c σ w : ℝ} (hc : c ≠ 0)
    (hσ : σ ^ 2 = 1) (hd : 0 ≤ b ^ 2 - 4 * c * a)
    (hw : b + 2 * c * w ≠ 0) (hsign : σ * (b + 2 * c * w) = |b + 2 * c * w|) :
    |w - (-b + σ * Real.sqrt (b ^ 2 - 4 * c * a)) / (2 * c)| ≤
      2 * |a + b * w + c * w ^ 2| / |b + 2 * c * w| := by
  let d := b + 2 * c * w
  let r := Real.sqrt (b ^ 2 - 4 * c * a)
  let f := (-b + σ * r) / (2 * c)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = b ^ 2 - 4 * c * a := Real.sq_sqrt hd
  have hdpos : 0 < |d| := abs_pos.mpr hw
  have hσabs : |σ| = 1 := by nlinarith [sq_abs σ, abs_nonneg σ]
  have hden : |d + σ * r| = |d| + r := by
    calc
      |d + σ * r| = |σ| * |d + σ * r| := by rw [hσabs, one_mul]
      _ = |σ * (d + σ * r)| := (abs_mul _ _).symm
      _ = |(|d| + r)| := by
        congr 1
        calc
          σ * (d + σ * r) = σ * d + σ ^ 2 * r := by ring
          _ = |d| + r := by rw [show σ * d = |d| from hsign, hσ, one_mul]
      _ = |d| + r := abs_of_nonneg (by positivity)
  have hdenpos : 0 < |d + σ * r| := by rw [hden]; positivity
  have h2c : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hid : (w - f) * (d + σ * r) = 2 * (a + b * w + c * w ^ 2) := by
    apply mul_right_cancel₀ h2c
    calc
      (w - f) * (d + σ * r) * (2 * c) = (d - σ * r) * (d + σ * r) := by
        dsimp [d, f]
        field_simp [hc]
        ring
      _ = d ^ 2 - r ^ 2 := by
        calc
          (d - σ * r) * (d + σ * r) = d ^ 2 - (σ * r) ^ 2 := by ring
          _ = d ^ 2 - r ^ 2 := by rw [mul_pow, hσ, one_mul]
      _ = 2 * (a + b * w + c * w ^ 2) * (2 * c) := by rw [hr2]; dsimp [d]; ring
  calc
    |w - f| = |(w - f) * (d + σ * r)| / |d + σ * r| := by
      rw [abs_mul, mul_div_cancel_right₀ _ hdenpos.ne']
    _ = 2 * |a + b * w + c * w ^ 2| / (|d| + r) := by rw [hid, abs_mul, hden]; norm_num
    _ ≤ 2 * |a + b * w + c * w ^ 2| / |d| :=
      div_le_div_of_nonneg_left (by positivity) hdpos (by linarith)

end Submission.Obl.k4_paired_test_normalization
