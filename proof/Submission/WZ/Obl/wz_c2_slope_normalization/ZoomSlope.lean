-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_c2_slope_normalization.ZoomSlope.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_c2_slope_normalization.ZoomRotate
import Submission.WZ.Obl.wz_c2_slope_normalization.AffineCutoff
import Submission.WZ.Obl.wz_c2_slope_normalization.Normalization

/-!
# The rotated slope

For a slope `g` with small first and second derivatives, rotating about the vertical axis by
`-arctan (g 0)` produces the slope `(g - g 0) / (1 + g * g 0)`.  Composing `g` with a smooth
clamp makes this a globally `C²` function, equal to the rotated slope on `[-2, 2]`, whose value
and first two derivatives are at most one on `[-1, 1]`.
-/

namespace WangZahlLot.Obl.wz_c2_slope_normalization

open Set Metric Filter Topology

noncomputable section

/-- A smooth clamp, the identity on `[-2, 2]` and with values in `[-3, 3]`. -/
def clampφ (t : ℝ) : ℝ := t * intervalCutoff (-2) 2 1 t

theorem clampφ_contDiff : ContDiff ℝ 2 clampφ :=
  contDiff_id.mul ((intervalCutoff_contDiff (-2) 2 1).of_le (by simp))

theorem clampφ_eq {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) : clampφ t = t := by
  rw [clampφ, intervalCutoff_eq_one one_pos (by simpa using ht), mul_one]

theorem abs_clampφ_le (t : ℝ) : |clampφ t| ≤ 3 := by
  rcases le_or_gt (|t|) 3 with h | h
  · rw [clampφ, abs_mul]
    have h1 := intervalCutoff_mem_Icc (-2) 2 1 t
    rw [abs_of_nonneg h1.1]
    have := mul_le_mul h h1.2 h1.1 (by norm_num)
    linarith
  · have h0 : clampφ t = 0 := by
      rw [clampφ, intervalCutoff_eq_zero one_pos, mul_zero]
      rcases lt_abs.mp h with h | h
      · right; linarith
      · left; linarith
    rw [h0, abs_zero]; norm_num

theorem clampφ_eventually {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : clampφ =ᶠ[𝓝 t] id := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact clampφ_eq (Ioo_subset_Icc_self hs)

/-- The rotated slope of `g` about the angle `-arctan (g 0)`, composed with the clamp. -/
def rotSlope (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (g (clampφ t) - g 0) / (1 + g (clampφ t) * g 0)

theorem lipschitz_of_deriv {g : ℝ → ℝ} {ε : ℝ} (hg : Differentiable ℝ g)
    (hd : ∀ t, |deriv g t| ≤ ε) (x y : ℝ) : |g x - g y| ≤ ε * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun t _ => hg t)
    (fun t _ => by simpa [Real.norm_eq_abs] using hd t) convex_univ (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- The denominator of the rotated slope stays at least half of `1 + g(0)²`. -/
theorem rotSlope_denom {g : ℝ → ℝ} {ε : ℝ} (hg : Differentiable ℝ g) (hε : ε ≤ 1 / 16)
    (hd : ∀ t, |deriv g t| ≤ ε) (t : ℝ) :
    (1 + g 0 ^ 2) / 2 ≤ 1 + g (clampφ t) * g 0 := by
  have h1 := lipschitz_of_deriv hg hd (clampφ t) 0
  rw [sub_zero] at h1
  have h2 : |g (clampφ t) - g 0| ≤ 3 / 16 := by
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hd 0)
    calc |g (clampφ t) - g 0| ≤ ε * |clampφ t| := h1
      _ ≤ (1 / 16) * 3 := mul_le_mul hε (abs_clampφ_le t) (abs_nonneg _) (by norm_num)
      _ = 3 / 16 := by norm_num
  have h3 : |(g (clampφ t) - g 0) * g 0| ≤ 3 / 16 * |g 0| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have h4 : |g 0| ≤ (1 + g 0 ^ 2) / 2 := by
    nlinarith [sq_nonneg (|g 0| - 1), sq_abs (g 0)]
  have h5 := neg_abs_le ((g (clampφ t) - g 0) * g 0)
  nlinarith [abs_nonneg (g 0)]

theorem differentiable_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) := by
  have h := hf.differentiable_iteratedDeriv 1 (by norm_num)
  rwa [iteratedDeriv_one] at h

theorem rotSlope_eq {g : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    rotSlope g t = (g t - g 0) / (1 + g t * g 0) := by
  rw [rotSlope, clampφ_eq ht]

/-- The rotated slope is a globally `C²` function whose value and first two derivatives are at
most one on `[-1, 1]`, provided the first two derivatives of `g` are at most `1/16`. -/
theorem rotSlope_normalized {g : ℝ → ℝ} {ε : ℝ} (hε : ε ≤ 1 / 16) (hg : ContDiff ℝ 2 g)
    (hd1 : ∀ t, |deriv g t| ≤ ε) (hd2 : ∀ t, |deriv (deriv g) t| ≤ ε) :
    NormalizedC2Slope (rotSlope g) := by
  set h0 := g 0
  set h := fun t => g (clampφ t)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hd1 0)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hh : ContDiff ℝ 2 h := hg.comp clampφ_contDiff
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hhd' : Differentiable ℝ (deriv h) := differentiable_deriv_of_contDiff_two hh
  have hden : ∀ t, (1 + h0 ^ 2) / 2 ≤ 1 + h t * h0 := fun t => rotSlope_denom hgd hε hd1 t
  have hA : 1 ≤ 1 + h0 ^ 2 := by nlinarith [sq_nonneg h0]
  have hpos : ∀ t, 0 < 1 + h t * h0 := fun t => by linarith [hden t]
  have hne : ∀ t, 1 + h t * h0 ≠ 0 := fun t => (hpos t).ne'
  have hR : rotSlope g = fun t => (h t - h0) / (1 + h t * h0) := rfl
  have hD : deriv (rotSlope g) = fun t => deriv h t * (1 + h0 ^ 2) / (1 + h t * h0) ^ 2 := by
    funext t
    have hht : HasDerivAt h (deriv h t) t := (hhd t).hasDerivAt
    have h1 : HasDerivAt (fun t => (h t - h0) / (1 + h t * h0)) _ t :=
      (hht.sub_const h0).div ((hht.mul_const h0).const_add 1) (hne t)
    rw [hR, h1.deriv]
    field_simp
    ring
  have hDD : deriv (deriv (rotSlope g)) = fun t =>
      (deriv (deriv h) t * (1 + h0 ^ 2) * (1 + h t * h0) ^ 2 -
        deriv h t * (1 + h0 ^ 2) * (2 * (1 + h t * h0) * (deriv h t * h0))) /
          ((1 + h t * h0) ^ 2) ^ 2 := by
    funext t
    have hht : HasDerivAt h (deriv h t) t := (hhd t).hasDerivAt
    have hht' : HasDerivAt (deriv h) (deriv (deriv h) t) t := (hhd' t).hasDerivAt
    have hden2 : HasDerivAt (fun t => (1 + h t * h0) ^ 2)
        (2 * (1 + h t * h0) * (deriv h t * h0)) t := by
      have := ((hht.mul_const h0).const_add 1).pow 2
      convert this using 1
      push_cast
      ring
    have h1 : HasDerivAt (fun t => deriv h t * (1 + h0 ^ 2) / (1 + h t * h0) ^ 2) _ t :=
      (hht'.mul_const (1 + h0 ^ 2)).div hden2 (pow_ne_zero 2 (hne t))
    rw [hD, h1.deriv]
  have hloc : ∀ t ∈ Icc (-1 : ℝ) 1, h =ᶠ[𝓝 t] g := by
    intro t ht
    have ht' : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    filter_upwards [clampφ_eventually ht'] with s hs
    simp only [h, hs, id]
  refine ⟨?_, ?_⟩
  · rw [hR]
    exact (hh.sub contDiff_const).div (contDiff_const.add (hh.mul contDiff_const)) hne
  intro t ht
  have hd1t : deriv h t = deriv g t := (hloc t ht).deriv_eq
  have hd2t : deriv (deriv h) t = deriv (deriv g) t :=
    ((hloc t ht).deriv).deriv_eq
  have hb1 : |deriv h t| ≤ ε := hd1t ▸ hd1 t
  have hb2 : |deriv (deriv h) t| ≤ ε := hd2t ▸ hd2 t
  have hdiff : |h t - h0| ≤ 3 / 16 := by
    have h1 := lipschitz_of_deriv hgd hd1 (clampφ t) 0
    rw [sub_zero] at h1
    calc |h t - h0| ≤ ε * |clampφ t| := h1
      _ ≤ (1 / 16) * 3 := mul_le_mul hε (abs_clampφ_le t) (abs_nonneg _) (by norm_num)
      _ = 3 / 16 := by norm_num
  have hh0 : |h0| ≤ 1 + h0 ^ 2 := by nlinarith [sq_nonneg (|h0| - 1), sq_abs h0, abs_nonneg h0]
  set A := 1 + h0 ^ 2
  set B := 1 + h t * h0
  have hBA : A / 2 ≤ B := hden t
  have hB0 : 0 < B := hpos t
  refine ⟨?_, ?_, ?_⟩
  · rw [hR]
    show |(h t - h0) / B| ≤ 1
    rw [abs_div, abs_of_pos hB0, div_le_one hB0]
    nlinarith
  · rw [hD]
    show |deriv h t * A / B ^ 2| ≤ 1
    have hA0 : 0 < A := by linarith
    rw [abs_div, abs_mul, abs_of_pos hA0, abs_of_pos (pow_pos hB0 2),
      div_le_one (pow_pos hB0 2)]
    have h1 : |deriv h t| * A ≤ ε * A := mul_le_mul_of_nonneg_right hb1 hA0.le
    have h2 : (A / 2) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) hBA 2
    nlinarith
  · rw [hDD]
    show |(deriv (deriv h) t * A * B ^ 2 - deriv h t * A * (2 * B * (deriv h t * h0))) /
      (B ^ 2) ^ 2| ≤ 1
    have hA0 : 0 < A := by linarith
    have hB4pos : 0 < (B ^ 2) ^ 2 := by positivity
    rw [abs_div, abs_of_pos hB4pos, div_le_one hB4pos]
    have hnum : |deriv (deriv h) t * A * B ^ 2 - deriv h t * A * (2 * B * (deriv h t * h0))| ≤
        ε * A * B ^ 2 + 2 * ε ^ 2 * A * B * A := by
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_pos hA0, abs_of_pos (pow_pos hB0 2)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 hA0.le)
          (pow_pos hB0 2).le
      · have e : deriv h t * A * (2 * B * (deriv h t * h0)) =
            2 * A * B * (deriv h t) ^ 2 * h0 := by ring
        rw [e, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos hA0, abs_of_pos hB0, abs_pow]
        have hsq : |deriv h t| ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb1 2
        calc 2 * A * B * |deriv h t| ^ 2 * |h0| ≤ 2 * A * B * ε ^ 2 * A := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hh0
                (abs_nonneg _) (by positivity)
          _ = 2 * ε ^ 2 * A * B * A := by ring
    refine hnum.trans ?_
    have hB1 : 1 / 2 ≤ B := by linarith
    have hAB : A ≤ 2 * B := by linarith
    have hεA : ε * A * B ^ 2 ≤ (1 / 8) * B ^ 3 := by
      have : ε * A ≤ (1 / 16) * (2 * B) := mul_le_mul hε hAB hA0.le (by norm_num)
      have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
      nlinarith
    have hε2 : 2 * ε ^ 2 * A * B * A ≤ (1 / 32) * B ^ 3 := by
      have h1 : ε ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hε0 hε 2
      have h2 : A * A ≤ (2 * B) * (2 * B) := mul_le_mul hAB hAB hA0.le (by positivity)
      have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
      have hB0' : 0 ≤ B := hB0.le
      nlinarith
    have hB3 : (1 / 8 + 1 / 32) * B ^ 3 ≤ (B ^ 2) ^ 2 := by
      have : B ^ 3 * (1 / 8 + 1 / 32) ≤ B ^ 3 * B := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      nlinarith
    linarith

end

end WangZahlLot.Obl.wz_c2_slope_normalization
