import Mathlib
import Submission.Obl.k4_conditional_common_affine_field.AnchorRows

set_option autoImplicit false

/-!
# The bilinear interpolant of two anchor rows

Grid coordinates: `b₁ = Y - t w₁`, `b₂ = Y - t w₂` are the intercepts of the two axis lines through
a point, so `b₁ - b₂ = t u` with `u = w₂ - w₁`.  A row is a strip of `b₁`, a column a strip of
`b₂`.  The selected option of a row at height `y` is an affine function of time
`h 0 + h 1 τ`; at the column with intercept `b₂` it is evaluated at the crossing time
`T = (y - b₂)/u`.  The interpolant of two anchor rows at heights `y₁ ≠ y₂` along the column of
`b₂`, evaluated at time `t`, is the bilinear function `bilCoeffs` of `(b₁, b₂)`.

* `bil_eq`: the identity between the interpolant and the bilinear coefficients.
* `anchor_fit`: deterministic core; a value fitting its column's affine function, in a column with
  fitted anchors near both anchor rows, is close to the interpolant.
* `interp_ratio_le`, `abs_bilCoeffs_le`: the explicit bounds.
-/

namespace Submission.Obl.k4_conditional_common_affine_field

/-- Coefficients `(β₀, β₁, β₂, β₃)` of the interpolant `β₀ + β₁ b₁ + β₂ b₂ + β₃ b₁ b₂` of the rows
with options `h₁, h₂` at heights `y₁, y₂`. -/
noncomputable def bilCoeffs (h₁ h₂ : Fin 3 → ℝ) (y₁ y₂ u : ℝ) : Fin 4 → ℝ :=
  ![(h₁ 0 + h₁ 1 * y₁ / u) - y₁ * ((h₂ 0 + h₂ 1 * y₂ / u) - (h₁ 0 + h₁ 1 * y₁ / u)) / (y₂ - y₁),
    ((h₂ 0 + h₂ 1 * y₂ / u) - (h₁ 0 + h₁ 1 * y₁ / u)) / (y₂ - y₁),
    -(h₁ 1 / u) - y₁ * (-(h₂ 1 / u) - -(h₁ 1 / u)) / (y₂ - y₁),
    (-(h₂ 1 / u) - -(h₁ 1 / u)) / (y₂ - y₁)]

/-- Evaluation of the bilinear function with coefficients `β`. -/
def bilEval (β : Fin 4 → ℝ) (b₁ b₂ : ℝ) : ℝ := β 0 + β 1 * b₁ + β 2 * b₂ + β 3 * b₁ * b₂

theorem bil_eq (h₁ h₂ : Fin 3 → ℝ) {y₁ y₂ u t b₁ b₂ : ℝ} (hu : u ≠ 0) (hy : y₁ ≠ y₂)
    (hrel : b₁ - b₂ = t * u) :
    bilEval (bilCoeffs h₁ h₂ y₁ y₂ u) b₁ b₂ =
      (h₁ 0 + h₁ 1 * ((y₁ - b₂) / u)) + (t - (y₁ - b₂) / u) *
        ((h₂ 0 + h₂ 1 * ((y₂ - b₂) / u)) - (h₁ 0 + h₁ 1 * ((y₁ - b₂) / u))) /
          ((y₂ - b₂) / u - (y₁ - b₂) / u) := by
  have hD : y₂ - y₁ ≠ 0 := sub_ne_zero.mpr hy.symm
  have ht : t = (b₁ - b₂) / u := by field_simp; linarith
  subst ht
  have hT : (y₂ - b₂) / u - (y₁ - b₂) / u = (y₂ - y₁) / u := by ring
  rw [hT]
  simp only [bilEval, bilCoeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-- **Deterministic core of the anchor interpolation.** -/
theorem anchor_fit {u y₁ y₂ t b₁ b₂ F₀ t' b₁' b₂' F₀' t'' b₁'' b₂'' F₀'' E B ω : ℝ}
    {V h₁ h₂ : Fin 3 → ℝ} (hu : u ≠ 0) (hy : y₁ ≠ y₂)
    (hrel : b₁ - b₂ = t * u) (hrel' : b₁' - b₂' = t' * u) (hrel'' : b₁'' - b₂'' = t'' * u)
    (hV : |F₀ - V 0 - V 1 * t| ≤ E)
    (hV' : |F₀' - V 0 - V 1 * t'| ≤ E) (hh' : |F₀' - h₁ 0 - h₁ 1 * t'| ≤ E)
    (hV'' : |F₀'' - V 0 - V 1 * t''| ≤ E) (hh'' : |F₀'' - h₂ 0 - h₂ 1 * t''| ≤ E)
    (hb₁' : |b₁' - y₁| ≤ ω) (hb₂' : |b₂' - b₂| ≤ ω) (hb₁'' : |b₁'' - y₂| ≤ ω)
    (hb₂'' : |b₂'' - b₂| ≤ ω)
    (hVB : |V 1| ≤ B) (hh₁B : |h₁ 1| ≤ B) (hh₂B : |h₂ 1| ≤ B) :
    |F₀ - bilEval (bilCoeffs h₁ h₂ y₁ y₂ u) b₁ b₂| ≤
      E + (2 * E + 4 * B * ω / |u|) * (|t - (y₁ - b₂) / u| + |t - (y₂ - b₂) / u|) /
        |(y₂ - b₂) / u - (y₁ - b₂) / u| := by
  have hupos : 0 < |u| := abs_pos.mpr hu
  set T₁ := (y₁ - b₂) / u with hT₁
  set T₂ := (y₂ - b₂) / u with hT₂
  have hT12 : T₁ ≠ T₂ := by
    intro h
    apply hy
    have := congrArg (· * u) h
    simp only [hT₁, hT₂] at this
    field_simp at this
    linarith
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hVB
  -- the anchors' times are near the crossing times
  have hclose : ∀ {s b₁s b₂s y : ℝ}, b₁s - b₂s = s * u → |b₁s - y| ≤ ω → |b₂s - b₂| ≤ ω →
      |s - (y - b₂) / u| ≤ 2 * ω / |u| := by
    intro s b₁s b₂s y hs h1 h2
    have hs' : s - (y - b₂) / u = ((b₁s - y) - (b₂s - b₂)) / u := by
      field_simp; linarith
    rw [hs', abs_div, div_le_div_iff_of_pos_right hupos]
    calc |(b₁s - y) - (b₂s - b₂)| ≤ |b₁s - y| + |b₂s - b₂| := abs_sub _ _
      _ ≤ ω + ω := add_le_add h1 h2
      _ = 2 * ω := by ring
  have hc' := hclose hrel' hb₁' hb₂'
  have hc'' := hclose hrel'' hb₁'' hb₂''
  -- the column function and the anchor rows agree at the crossing times
  have hagree : ∀ {s F' : ℝ} {h : Fin 3 → ℝ} {T : ℝ}, |F' - V 0 - V 1 * s| ≤ E →
      |F' - h 0 - h 1 * s| ≤ E → |h 1| ≤ B → |s - T| ≤ 2 * ω / |u| →
      |(V 0 + V 1 * T) - (h 0 + h 1 * T)| ≤ 2 * E + 4 * B * ω / |u| := by
    intro s F' h T h1 h2 hhB hsT
    have heq : (V 0 + V 1 * T) - (h 0 + h 1 * T) =
        -(F' - V 0 - V 1 * s) + (F' - h 0 - h 1 * s) - V 1 * (s - T) + h 1 * (s - T) := by ring
    rw [heq]
    have hm1 : |V 1 * (s - T)| ≤ B * (2 * ω / |u|) := by
      rw [abs_mul]; exact mul_le_mul hVB hsT (abs_nonneg _) hB0
    have hm2 : |h 1 * (s - T)| ≤ B * (2 * ω / |u|) := by
      rw [abs_mul]; exact mul_le_mul hhB hsT (abs_nonneg _) hB0
    calc |-(F' - V 0 - V 1 * s) + (F' - h 0 - h 1 * s) - V 1 * (s - T) + h 1 * (s - T)|
        ≤ |-(F' - V 0 - V 1 * s)| + |F' - h 0 - h 1 * s| + |V 1 * (s - T)| + |h 1 * (s - T)| := by
          have := abs_add_le (-(F' - V 0 - V 1 * s) + (F' - h 0 - h 1 * s) - V 1 * (s - T))
            (h 1 * (s - T))
          have := abs_sub (-(F' - V 0 - V 1 * s) + (F' - h 0 - h 1 * s)) (V 1 * (s - T))
          have := abs_add_le (-(F' - V 0 - V 1 * s)) (F' - h 0 - h 1 * s)
          linarith
      _ ≤ E + E + B * (2 * ω / |u|) + B * (2 * ω / |u|) := by
          rw [abs_neg]; linarith
      _ = 2 * E + 4 * B * ω / |u| := by ring
  have hA₁ := hagree hV' hh' hh₁B hc'
  have hA₂ := hagree hV'' hh'' hh₂B hc''
  -- the difference of the column function and the interpolant is affine in time
  set H₁ := h₁ 0 + h₁ 1 * T₁ with hH₁
  set H₂ := h₂ 0 + h₂ 1 * T₂ with hH₂
  set Sl := (H₂ - H₁) / (T₂ - T₁) with hSl
  have hTd : T₂ - T₁ ≠ 0 := sub_ne_zero.mpr hT12.symm
  have hSl' : (T₂ - T₁) * Sl = H₂ - H₁ := by rw [hSl]; field_simp
  have hD₁ : |(V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * T₁| ≤ 2 * E + 4 * B * ω / |u| := by
    have : (V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * T₁ = (V 0 + V 1 * T₁) - (h₁ 0 + h₁ 1 * T₁) := by
      rw [hH₁]; ring
    rw [this]; exact hA₁
  have hD₂ : |(V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * T₂| ≤ 2 * E + 4 * B * ω / |u| := by
    have : (V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * T₂ = (V 0 + V 1 * T₂) - (h₂ 0 + h₂ 1 * T₂) := by
      have h2 : H₂ = H₁ + (T₂ - T₁) * Sl := by rw [hSl']; ring
      rw [hH₂] at h2
      linear_combination h2
    rw [this]; exact hA₂
  have hint := affine_interp_bound hT12 hD₁ hD₂ (y := t)
  rw [bil_eq h₁ h₂ hu hy hrel]
  have heq : F₀ - (H₁ + (t - T₁) * (H₂ - H₁) / (T₂ - T₁)) =
      (F₀ - V 0 - V 1 * t) + ((V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * t) := by
    rw [hSl]; ring
  rw [heq]
  calc |(F₀ - V 0 - V 1 * t) + ((V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * t)|
      ≤ |F₀ - V 0 - V 1 * t| + |(V 0 - H₁ + T₁ * Sl) + (V 1 - Sl) * t| := abs_add_le _ _
    _ ≤ E + (2 * E + 4 * B * ω / |u|) * (|t - T₁| + |t - T₂|) / |T₂ - T₁| := add_le_add hV hint

/-- The interpolation ratio is bounded through the row separation. -/
theorem interp_ratio_le {u y₁ y₂ t b₂ B γ : ℝ} (hu : u ≠ 0) (hγ : 0 < γ) (ht : |t| ≤ 1)
    (hy₁ : |y₁| ≤ 2 * B) (hy₂ : |y₂| ≤ 2 * B) (hb₂ : |b₂| ≤ B) (hsep : γ ≤ |y₁ - y₂|) :
    (|t - (y₁ - b₂) / u| + |t - (y₂ - b₂) / u|) / |(y₂ - b₂) / u - (y₁ - b₂) / u| ≤
      2 * (|u| + 3 * B) / γ := by
  have hupos : 0 < |u| := abs_pos.mpr hu
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hb₂
  have hT : (y₂ - b₂) / u - (y₁ - b₂) / u = (y₂ - y₁) / u := by ring
  rw [hT, abs_div, abs_sub_comm y₂ y₁]
  have hsep' : 0 < |y₁ - y₂| := lt_of_lt_of_le hγ hsep
  have hk : ∀ y, |y| ≤ 2 * B → |t - (y - b₂) / u| ≤ (|u| + 3 * B) / |u| := by
    intro y hy
    rw [le_div_iff₀ hupos]
    calc |t - (y - b₂) / u| * |u| = |t * u - (y - b₂)| := by
          rw [← abs_mul]; congr 1; field_simp
      _ ≤ |t * u| + |y - b₂| := abs_sub _ _
      _ ≤ |u| + (|y| + |b₂|) := by
          have h1 : |t * u| ≤ |u| := by
            rw [abs_mul]; nlinarith [abs_nonneg u, abs_nonneg t]
          have h2 : |y - b₂| ≤ |y| + |b₂| := abs_sub _ _
          linarith
      _ ≤ |u| + 3 * B := by linarith
  rw [div_div_eq_mul_div, div_le_div_iff₀ hsep' hγ]
  calc (|t - (y₁ - b₂) / u| + |t - (y₂ - b₂) / u|) * |u| * γ
      ≤ ((|u| + 3 * B) / |u| + (|u| + 3 * B) / |u|) * |u| * |y₁ - y₂| := by
        have h1 := hk y₁ hy₁
        have h2 := hk y₂ hy₂
        apply mul_le_mul _ hsep hγ.le (by positivity)
        exact mul_le_mul_of_nonneg_right (add_le_add h1 h2) hupos.le
    _ = 2 * (|u| + 3 * B) * |y₁ - y₂| := by field_simp; ring

/-- Coefficient bounds of the interpolant. -/
theorem abs_bilCoeffs_le (h₁ h₂ : Fin 3 → ℝ) {y₁ y₂ u B γ : ℝ} (hu : u ≠ 0) (hγ : 0 < γ)
    (hB : 1 ≤ B) (hh₁ : ∀ k, |h₁ k| ≤ B) (hh₂ : ∀ k, |h₂ k| ≤ B) (hy₁ : |y₁| ≤ 2 * B)
    (hy₂ : |y₂| ≤ 2 * B) (hsep : γ ≤ |y₁ - y₂|) (k : Fin 4) :
    |bilCoeffs h₁ h₂ y₁ y₂ u k| ≤ 12 * B ^ 3 * (1 + 1 / |u|) * (1 + 1 / γ) := by
  have hupos : 0 < |u| := abs_pos.mpr hu
  set x := 1 / |u| with hx
  set g := 1 / γ with hg
  have hx0 : 0 ≤ x := by positivity
  have hg0 : 0 ≤ g := by positivity
  have hB0 : 0 ≤ B := by linarith
  have hD : 0 < |y₂ - y₁| := by rw [abs_sub_comm]; linarith
  have hdivu : ∀ q : ℝ, |q / u| = |q| * x := by
    intro q; rw [abs_div, hx]; field_simp
  have hdivD : ∀ q : ℝ, |q / (y₂ - y₁)| ≤ |q| * g := by
    intro q
    rw [abs_div, hg, div_le_iff₀ hD]
    have : |q| * (1 / γ) * |y₂ - y₁| = |q| * (|y₂ - y₁| / γ) := by ring
    rw [this]
    have h1 : 1 ≤ |y₂ - y₁| / γ := by
      rw [le_div_iff₀ hγ, abs_sub_comm]; linarith
    nlinarith [abs_nonneg q]
  -- the four ingredients
  have hA0 : |h₁ 0 + h₁ 1 * y₁ / u| ≤ B + 2 * B ^ 2 * x := by
    calc |h₁ 0 + h₁ 1 * y₁ / u| ≤ |h₁ 0| + |h₁ 1 * y₁ / u| := abs_add_le _ _
      _ = |h₁ 0| + |h₁ 1| * |y₁| * x := by rw [hdivu, abs_mul]
      _ ≤ B + B * (2 * B) * x := by gcongr; exact hh₁ 0; exact hh₁ 1
      _ = B + 2 * B ^ 2 * x := by ring
  have hB0' : |h₂ 0 + h₂ 1 * y₂ / u| ≤ B + 2 * B ^ 2 * x := by
    calc |h₂ 0 + h₂ 1 * y₂ / u| ≤ |h₂ 0| + |h₂ 1 * y₂ / u| := abs_add_le _ _
      _ = |h₂ 0| + |h₂ 1| * |y₂| * x := by rw [hdivu, abs_mul]
      _ ≤ B + B * (2 * B) * x := by gcongr; exact hh₂ 0; exact hh₂ 1
      _ = B + 2 * B ^ 2 * x := by ring
  have hA1 : |-(h₁ 1 / u)| ≤ B * x := by rw [abs_neg, hdivu]; gcongr; exact hh₁ 1
  have hB1 : |-(h₂ 1 / u)| ≤ B * x := by rw [abs_neg, hdivu]; gcongr; exact hh₂ 1
  have hdiff0 : |(h₂ 0 + h₂ 1 * y₂ / u) - (h₁ 0 + h₁ 1 * y₁ / u)| ≤ 2 * (B + 2 * B ^ 2 * x) := by
    calc _ ≤ |h₂ 0 + h₂ 1 * y₂ / u| + |h₁ 0 + h₁ 1 * y₁ / u| := abs_sub _ _
      _ ≤ _ := by linarith
  have hdiff1 : |-(h₂ 1 / u) - -(h₁ 1 / u)| ≤ 2 * (B * x) := by
    calc _ ≤ |-(h₂ 1 / u)| + |-(h₁ 1 / u)| := abs_sub _ _
      _ ≤ _ := by linarith
  have hβ1 : |((h₂ 0 + h₂ 1 * y₂ / u) - (h₁ 0 + h₁ 1 * y₁ / u)) / (y₂ - y₁)| ≤
      2 * (B + 2 * B ^ 2 * x) * g :=
    (hdivD _).trans (by gcongr)
  have hβ3 : |(-(h₂ 1 / u) - -(h₁ 1 / u)) / (y₂ - y₁)| ≤ 2 * (B * x) * g :=
    (hdivD _).trans (by gcongr)
  have hfinal : B + 2 * B ^ 2 * x + 2 * B * (2 * (B + 2 * B ^ 2 * x) * g) ≤
      12 * B ^ 3 * (1 + x) * (1 + g) := by
    have hB2 : B ≤ B ^ 3 := by nlinarith
    have hB22 : B ^ 2 ≤ B ^ 3 := by nlinarith
    nlinarith [mul_nonneg hx0 hg0, mul_nonneg (mul_nonneg hx0 hg0) hB0]
  have hfinal' : B * x + 2 * B * (2 * (B * x) * g) ≤ 12 * B ^ 3 * (1 + x) * (1 + g) := by
    have hB2 : B ≤ B ^ 3 := by nlinarith
    have hB22 : B ^ 2 ≤ B ^ 3 := by nlinarith
    nlinarith [mul_nonneg hx0 hg0, mul_nonneg (mul_nonneg hx0 hg0) hB0]
  have hbig : 0 ≤ 12 * B ^ 3 * (1 + x) * (1 + g) := by positivity
  fin_cases k
  · simp only [bilCoeffs, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    have hmul : |y₁ * ((h₂ 0 + h₂ 1 * y₂ / u) - (h₁ 0 + h₁ 1 * y₁ / u)) / (y₂ - y₁)| ≤
        2 * B * (2 * (B + 2 * B ^ 2 * x) * g) := by
      rw [mul_div_assoc, abs_mul]
      exact mul_le_mul hy₁ hβ1 (abs_nonneg _) (by positivity)
    calc _ ≤ |h₁ 0 + h₁ 1 * y₁ / u| + |y₁ * ((h₂ 0 + h₂ 1 * y₂ / u) - (h₁ 0 + h₁ 1 * y₁ / u)) /
          (y₂ - y₁)| := abs_sub _ _
      _ ≤ B + 2 * B ^ 2 * x + 2 * B * (2 * (B + 2 * B ^ 2 * x) * g) := add_le_add hA0 hmul
      _ ≤ _ := hfinal
  · simp only [bilCoeffs, Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
    refine hβ1.trans ?_
    nlinarith [mul_nonneg hx0 hg0, mul_nonneg (mul_nonneg hx0 hg0) hB0]
  · simp only [bilCoeffs, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    have hmul : |y₁ * (-(h₂ 1 / u) - -(h₁ 1 / u)) / (y₂ - y₁)| ≤ 2 * B * (2 * (B * x) * g) := by
      rw [mul_div_assoc, abs_mul]
      exact mul_le_mul hy₁ hβ3 (abs_nonneg _) (by positivity)
    calc _ ≤ |-(h₁ 1 / u)| + |y₁ * (-(h₂ 1 / u) - -(h₁ 1 / u)) / (y₂ - y₁)| := abs_sub _ _
      _ ≤ B * x + 2 * B * (2 * (B * x) * g) := add_le_add hA1 hmul
      _ ≤ _ := hfinal'
  · simp only [bilCoeffs, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons]
    refine hβ3.trans ?_
    nlinarith [mul_nonneg hx0 hg0, mul_nonneg (mul_nonneg hx0 hg0) hB0]

end Submission.Obl.k4_conditional_common_affine_field
