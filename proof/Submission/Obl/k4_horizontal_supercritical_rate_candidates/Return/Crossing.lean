import Mathlib
import Submission.Lib.K4QuadraticSublevel

/-!
# Steep quadratic laws cannot sit in sparse flat slabs

A quadratic `g` on an interval of length `H` whose values stay within `E` of a finite
set of slab levels on a set of heights of measure at least `θ * H` has small oscillation,
provided every window of width `W ≥ a₀` contains at most `Cs * (W / a₀) ^ d` levels with
`d < 1`. This is the counting step that forces a supercritical projected label to share
the vertical structure of the coarse true labels.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open Set MeasureTheory
open Submission.Lib.K4QuadraticSublevel

noncomputable section

/-- The explicit quadratic `α + β (y - c) + γ (y - c)^2`. -/
def quad (α β γ c y : ℝ) : ℝ := α + β * (y - c) + γ * (y - c) ^ 2

/-- Its polynomial form, used for the sublevel lemma. -/
def quadPoly (α β γ c : ℝ) : Polynomial ℝ :=
  Polynomial.C γ * Polynomial.X ^ 2 + Polynomial.C (β - 2 * γ * c) * Polynomial.X +
    Polynomial.C (α - β * c + γ * c ^ 2)

theorem quadPoly_natDegree (α β γ c : ℝ) : (quadPoly α β γ c).natDegree ≤ 2 := by
  unfold quadPoly
  compute_degree

theorem quadPoly_eval (α β γ c y : ℝ) : (quadPoly α β γ c).eval y = quad α β γ c y := by
  unfold quadPoly quad
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  ring

theorem quadPoly_derivative_eval (α β γ c y : ℝ) :
    (quadPoly α β γ c).derivative.eval y = β + 2 * γ * (y - c) := by
  unfold quadPoly
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_zero, zero_mul, zero_add, mul_one]
  push_cast
  ring

/-- Sublevel set of `|g - ℓ| ≤ E` where `|g'| ≥ b`, measured. -/
theorem volume_quad_sublevel (α β γ c ℓ : ℝ) {E b : ℝ} (hE : 0 ≤ E) (hb : 0 < b) :
    volume {y : ℝ | |quad α β γ c y - ℓ| ≤ E ∧ b ≤ |β + 2 * γ * (y - c)|} ≤
      ENNReal.ofReal (4 * E / b) := by
  have h := volume_quadratic_sublevel (quadPoly (α - ℓ) β γ c) (quadPoly_natDegree _ _ _ _)
    hE hb
  refine le_trans (measure_mono ?_) h
  intro y hy
  simp only [mem_ofPred_eq, quadPoly_eval, quadPoly_derivative_eval] at hy ⊢
  refine ⟨?_, hy.2⟩
  have : quad (α - ℓ) β γ c y = quad α β γ c y - ℓ := by unfold quad; ring
  rw [this]; exact hy.1

/-- The set where an affine function is small is short. -/
theorem volume_affine_small (a b' : ℝ) {lam : ℝ} (ha : a ≠ 0) (hlam : 0 ≤ lam) :
    volume {y : ℝ | |b' + a * y| < lam} ≤ ENNReal.ofReal (2 * lam / |a|) := by
  have hsub : {y : ℝ | |b' + a * y| < lam} ⊆
      Icc ((-b' - lam) / a ⊓ (-b' + lam) / a) ((-b' - lam) / a ⊔ (-b' + lam) / a) := by
    intro y hy
    simp only [mem_ofPred_eq, abs_lt] at hy
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · constructor
      · refine inf_le_right.trans ?_
        rw [div_le_iff_of_neg hneg]; linarith
      · refine le_trans ?_ le_sup_left
        rw [le_div_iff_of_neg hneg]; linarith
    · constructor
      · refine inf_le_left.trans ?_
        rw [div_le_iff₀ hpos]; linarith
      · refine le_trans ?_ le_sup_right
        rw [le_div_iff₀ hpos]; linarith
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc]
  apply ENNReal.ofReal_le_ofReal
  have hd : ((-b' - lam) / a ⊔ (-b' + lam) / a) - ((-b' - lam) / a ⊓ (-b' + lam) / a) =
      |(-b' + lam) / a - (-b' - lam) / a| := by
    rw [max_sub_min_eq_abs', abs_sub_comm]
  rw [hd]
  have : (-b' + lam) / a - (-b' - lam) / a = 2 * lam / a := by
    field_simp; ring
  rw [this, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * lam)]

/-- On the centered interval the quadratic deviates from its center value by at most half of
`|β| H + |γ| H^2 / 2`. -/
theorem quad_sub_center_le (α β γ c y H : ℝ) (hy : y ∈ Icc (c - H / 2) (c + H / 2)) :
    |quad α β γ c y - α| ≤ (|β| * H + |γ| * H ^ 2 / 2) / 2 := by
  have hyc : |y - c| ≤ H / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hH : 0 ≤ H := by linarith [hy.1, hy.2]
  unfold quad
  have hsq : (y - c) ^ 2 ≤ (H / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hyc 2
  calc |α + β * (y - c) + γ * (y - c) ^ 2 - α| = |β * (y - c) + γ * (y - c) ^ 2| := by
        ring_nf
    _ ≤ |β| * |y - c| + |γ| * (y - c) ^ 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (y - c))]
    _ ≤ |β| * (H / 2) + |γ| * (H / 2) ^ 2 := by
        gcongr
    _ = (|β| * H + |γ| * H ^ 2 / 2) / 2 := by ring

/-- Crossing estimate: the quadratic's oscillation size `|β| H + |γ| H^2/2` is at most
`B * a₀` whenever its `e * a₀`-sublevel sets around sparse slab levels have measure
at least `θ H` in the interval. -/
theorem crossing_osc_bound {d e a₀ H θ Cs : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (ha₀ : 0 < a₀)
    (he : 0 ≤ e) (hH : 0 < H) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hCs : 0 ≤ Cs)
    (α β γ c : ℝ) (J : Finset ℝ)
    (hcount : ∀ w W : ℝ, a₀ ≤ W →
      ((J.filter (fun ℓ => w ≤ ℓ ∧ ℓ ≤ w + W)).card : ℝ) ≤ Cs * (W / a₀) ^ d)
    (hS : ENNReal.ofReal (θ * H) ≤ volume {y : ℝ | y ∈ Icc (c - H / 2) (c + H / 2) ∧
      ∃ ℓ ∈ J, |quad α β γ c y - ℓ| ≤ e * a₀}) :
    |β| * H + |γ| * H ^ 2 / 2 ≤
      max 1 ((2 * e + 40 * e * Cs / θ ^ 2) ^ (1 / (1 - d))) * a₀ := by
  classical
  set E := e * a₀ with hEdef
  have hE : 0 ≤ E := mul_nonneg he ha₀.le
  set W₀ := |β| * H + |γ| * H ^ 2 / 2 with hW₀def
  have hW₀ : 0 ≤ W₀ := by positivity
  set W := max (W₀ + 2 * E) a₀ with hWdef
  have hWa : a₀ ≤ W := le_max_right _ _
  set Jr := J.filter (fun ℓ => (α - W₀ / 2 - E) ≤ ℓ ∧ ℓ ≤ (α - W₀ / 2 - E) + W) with hJr
  have hcard : (Jr.card : ℝ) ≤ Cs * (W / a₀) ^ d := hcount _ _ hWa
  -- the sublevel set only sees relevant levels
  have hrel : ∀ y ∈ Icc (c - H / 2) (c + H / 2), ∀ ℓ ∈ J, |quad α β γ c y - ℓ| ≤ E → ℓ ∈ Jr := by
    intro y hy ℓ hℓ hyl
    have h1 := quad_sub_center_le α β γ c y H hy
    rw [hJr, Finset.mem_filter]
    refine ⟨hℓ, ?_, ?_⟩
    · have := abs_le.mp h1; have := abs_le.mp hyl; linarith
    · have := abs_le.mp h1; have := abs_le.mp hyl
      have : W₀ + 2 * E ≤ W := le_max_left _ _
      linarith
  -- key inequality: W₀ ≤ 40 * E * card / θ^2
  have hkey : W₀ ≤ 40 * E * (Jr.card : ℝ) / θ ^ 2 := by
    set S := {y : ℝ | y ∈ Icc (c - H / 2) (c + H / 2) ∧ ∃ ℓ ∈ J, |quad α β γ c y - ℓ| ≤ E}
    have hθH : 0 < θ * H := mul_pos hθ hH
    by_cases hcase : |γ| * H ≤ |β| / 2
    · -- linear-dominated case
      by_cases hβ : β = 0
      · have hγ : |γ| * H ≤ 0 := by simpa [hβ] using hcase
        have hγ0 : γ = 0 := by
          have : |γ| ≤ 0 := by
            by_contra hc; push Not at hc; nlinarith
          exact abs_nonpos_iff.mp this
        have : W₀ = 0 := by rw [hW₀def, hβ, hγ0]; simp
        rw [this]; positivity
      · have hβpos : 0 < |β| := abs_pos.mpr hβ
        set lam := |β| / 2 with hlam
        have hlampos : 0 < lam := by positivity
        have hsub : S ⊆ ⋃ ℓ ∈ Jr, {y : ℝ | |quad α β γ c y - ℓ| ≤ E ∧
            lam ≤ |β + 2 * γ * (y - c)|} := by
          intro y hy
          obtain ⟨hyI, ℓ, hℓ, hyl⟩ := hy
          refine Set.mem_biUnion (hrel y hyI ℓ hℓ hyl) ⟨hyl, ?_⟩
          have hyc : |y - c| ≤ H / 2 := abs_le.mpr ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
          have h2 : |2 * γ * (y - c)| ≤ |γ| * H := by
            rw [abs_mul, abs_mul, abs_two]; nlinarith [abs_nonneg γ]
          have := abs_sub_abs_le_abs_sub β (-(2 * γ * (y - c)))
          rw [sub_neg_eq_add, abs_neg] at this
          linarith
        have hvol : volume S ≤ (Jr.card : ENNReal) * ENNReal.ofReal (4 * E / lam) := by
          refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
          calc ∑ ℓ ∈ Jr, volume {y : ℝ | |quad α β γ c y - ℓ| ≤ E ∧
                lam ≤ |β + 2 * γ * (y - c)|}
              ≤ ∑ _ℓ ∈ Jr, ENNReal.ofReal (4 * E / lam) :=
                Finset.sum_le_sum (fun ℓ _ => volume_quad_sublevel α β γ c ℓ hE hlampos)
            _ = (Jr.card : ENNReal) * ENNReal.ofReal (4 * E / lam) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hreal : θ * H ≤ (Jr.card : ℝ) * (4 * E / lam) := by
          have := hS.trans hvol
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at this
          exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
        have hβH : |β| * H ≤ 8 * E * (Jr.card : ℝ) / θ := by
          rw [le_div_iff₀ hθ]
          have : (Jr.card : ℝ) * (4 * E / lam) = 8 * E * (Jr.card : ℝ) / |β| := by
            rw [hlam]; field_simp; ring
          rw [this, le_div_iff₀ hβpos] at hreal
          nlinarith
        have hγH : |γ| * H ^ 2 / 2 ≤ |β| * H / 4 := by
          have := mul_le_mul_of_nonneg_right hcase hH.le
          nlinarith
        have hθ2 : θ ^ 2 ≤ θ := by nlinarith
        calc W₀ = |β| * H + |γ| * H ^ 2 / 2 := rfl
          _ ≤ |β| * H + |β| * H / 4 := by linarith
          _ ≤ 10 * E * (Jr.card : ℝ) / θ := by
              have : |β| * H * (5 / 4) ≤ 8 * E * (Jr.card : ℝ) / θ * (5 / 4) := by
                nlinarith
              calc |β| * H + |β| * H / 4 = |β| * H * (5 / 4) := by ring
                _ ≤ 8 * E * (Jr.card : ℝ) / θ * (5 / 4) := this
                _ = 10 * E * (Jr.card : ℝ) / θ := by ring
          _ ≤ 40 * E * (Jr.card : ℝ) / θ ^ 2 := by
              rw [div_le_div_iff₀ hθ (by positivity)]
              have h0 : 0 ≤ E * (Jr.card : ℝ) := by positivity
              nlinarith
    · -- curvature-dominated case
      push Not at hcase
      have hγpos : 0 < |γ| := by
        by_contra hc; push Not at hc
        have : |γ| * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hH.le
        linarith [abs_nonneg β]
      have hγ0 : γ ≠ 0 := abs_pos.mp hγpos
      set lam := θ * |γ| * H / 2 with hlam
      have hlampos : 0 < lam := by positivity
      have hsub : S ⊆ {y : ℝ | |(β - 2 * γ * c) + (2 * γ) * y| < lam} ∪
          ⋃ ℓ ∈ Jr, {y : ℝ | |quad α β γ c y - ℓ| ≤ E ∧ lam ≤ |β + 2 * γ * (y - c)|} := by
        intro y hy
        obtain ⟨hyI, ℓ, hℓ, hyl⟩ := hy
        by_cases hsmall : |β + 2 * γ * (y - c)| < lam
        · left
          show |(β - 2 * γ * c) + (2 * γ) * y| < lam
          have : (β - 2 * γ * c) + (2 * γ) * y = β + 2 * γ * (y - c) := by ring
          rw [this]; exact hsmall
        · right
          push Not at hsmall
          exact Set.mem_biUnion (hrel y hyI ℓ hℓ hyl) ⟨hyl, hsmall⟩
      have h2γ : (2 * γ) ≠ 0 := mul_ne_zero two_ne_zero hγ0
      have hvol : volume S ≤ ENNReal.ofReal (2 * lam / |2 * γ|) +
          (Jr.card : ENNReal) * ENNReal.ofReal (4 * E / lam) := by
        refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
        · exact volume_affine_small (2 * γ) (β - 2 * γ * c) h2γ hlampos.le
        · refine (measure_biUnion_finset_le _ _).trans ?_
          calc ∑ ℓ ∈ Jr, volume {y : ℝ | |quad α β γ c y - ℓ| ≤ E ∧
                lam ≤ |β + 2 * γ * (y - c)|}
              ≤ ∑ _ℓ ∈ Jr, ENNReal.ofReal (4 * E / lam) :=
                Finset.sum_le_sum (fun ℓ _ => volume_quad_sublevel α β γ c ℓ hE hlampos)
            _ = (Jr.card : ENNReal) * ENNReal.ofReal (4 * E / lam) := by
                rw [Finset.sum_const, nsmul_eq_mul]
      have hreal : θ * H ≤ 2 * lam / |2 * γ| + (Jr.card : ℝ) * (4 * E / lam) := by
        have := hS.trans hvol
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)] at this
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
      have hfirst : 2 * lam / |2 * γ| = θ * H / 2 := by
        rw [hlam, abs_mul, abs_two]; field_simp
      have hsecond : (Jr.card : ℝ) * (4 * E / lam) = 8 * E * (Jr.card : ℝ) / (θ * |γ| * H) := by
        rw [hlam]; field_simp; ring
      rw [hfirst, hsecond] at hreal
      have hγH : |γ| * H ^ 2 ≤ 16 * E * (Jr.card : ℝ) / θ ^ 2 := by
        have hpos : 0 < θ * |γ| * H := by positivity
        have h1 : θ * H / 2 ≤ 8 * E * (Jr.card : ℝ) / (θ * |γ| * H) := by linarith
        rw [le_div_iff₀ hpos] at h1
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have hβH : |β| * H < 2 * (|γ| * H ^ 2) := by
        have := mul_lt_mul_of_pos_right hcase hH
        nlinarith
      calc W₀ = |β| * H + |γ| * H ^ 2 / 2 := rfl
        _ ≤ 5 / 2 * (|γ| * H ^ 2) := by linarith
        _ ≤ 5 / 2 * (16 * E * (Jr.card : ℝ) / θ ^ 2) := by linarith
        _ = 40 * E * (Jr.card : ℝ) / θ ^ 2 := by ring
  -- conclude with the power estimate
  have hX1 : 1 ≤ W / a₀ := by rw [le_div_iff₀ ha₀]; linarith
  have hXd : 1 ≤ (W / a₀) ^ d := Real.one_le_rpow hX1 hd0
  set Y := 2 * e + 40 * e * Cs / θ ^ 2 with hYdef
  have hY0 : 0 ≤ Y := by positivity
  by_cases hWcase : W₀ + 2 * E ≤ a₀
  · have : W₀ ≤ a₀ := by linarith
    calc W₀ ≤ 1 * a₀ := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) ha₀.le
  · push Not at hWcase
    have hWeq : W = W₀ + 2 * E := max_eq_left hWcase.le
    have hXeq : W / a₀ = W₀ / a₀ + 2 * e := by
      rw [hWeq, hEdef]; field_simp
    have hW₀a : W₀ / a₀ ≤ 40 * e * Cs * (W / a₀) ^ d / θ ^ 2 := by
      rw [div_le_iff₀ ha₀]
      calc W₀ ≤ 40 * E * (Jr.card : ℝ) / θ ^ 2 := hkey
        _ ≤ 40 * E * (Cs * (W / a₀) ^ d) / θ ^ 2 := by gcongr
        _ = 40 * e * Cs * (W / a₀) ^ d / θ ^ 2 * a₀ := by rw [hEdef]; ring
    have hXle : W / a₀ ≤ Y * (W / a₀) ^ d := by
      have h1 : 2 * e ≤ 2 * e * (W / a₀) ^ d := le_mul_of_one_le_right (by positivity) hXd
      calc W / a₀ = W₀ / a₀ + 2 * e := hXeq
        _ ≤ 40 * e * Cs * (W / a₀) ^ d / θ ^ 2 + 2 * e * (W / a₀) ^ d := add_le_add hW₀a h1
        _ = Y * (W / a₀) ^ d := by rw [hYdef]; ring
    have hXpos : 0 < W / a₀ := by linarith
    have hpow : (W / a₀) ^ (1 - d) ≤ Y := by
      have hsplit : W / a₀ = (W / a₀) ^ d * (W / a₀) ^ (1 - d) := by
        rw [← Real.rpow_add hXpos]; simp
      have hdpos : 0 < (W / a₀) ^ d := Real.rpow_pos_of_pos hXpos d
      have : (W / a₀) ^ d * (W / a₀) ^ (1 - d) ≤ (W / a₀) ^ d * Y := by
        rw [← hsplit]; linarith
      exact le_of_mul_le_mul_left this hdpos
    have h1d : 0 < 1 - d := by linarith
    have hXY : W / a₀ ≤ Y ^ (1 / (1 - d)) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le (1 - d)) hpow
        (show 0 ≤ 1 / (1 - d) by positivity)
      rwa [← Real.rpow_mul hXpos.le, mul_one_div_cancel h1d.ne', Real.rpow_one] at this
    have hW₀W : W₀ ≤ W := by rw [hWeq]; linarith
    calc W₀ ≤ W := hW₀W
      _ = (W / a₀) * a₀ := by field_simp
      _ ≤ Y ^ (1 / (1 - d)) * a₀ := mul_le_mul_of_nonneg_right hXY ha₀.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) ha₀.le

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
