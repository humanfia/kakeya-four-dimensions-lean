import Mathlib
import Submission.Lib.K4PolynomialRemez

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric MeasureTheory

/-- Relative proximity to a point on a ray forces a small transverse
coordinate, uniformly in the distance of that point from the origin. -/
theorem relative_ray_transverse {v r c : ℂ} {t δ : ℝ}
    (hc : ‖c‖ = 1) (hcr : c * r = (‖r‖ : ℂ))
    (ht : 0 ≤ t) (hv : ‖v‖ ≤ 1) (hδ : δ ≤ 1 / 2)
    (hnear : ‖(t : ℂ) * v - r‖ < δ * ‖r‖) :
    |(c * v).im| < 2 * δ := by
  have hrpos : 0 < ‖r‖ := by
    by_contra h
    have hr : ‖r‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hr, mul_zero] at hnear
    exact (norm_nonneg _).not_gt hnear
  have hδpos : 0 < δ := by
    nlinarith [norm_nonneg ((t : ℂ) * v - r)]
  have htri : ‖r‖ ≤ t * ‖v‖ + ‖(t : ℂ) * v - r‖ := by
    have h := norm_add_le ((t : ℂ) * v) (r - (t : ℂ) * v)
    rw [add_sub_cancel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
      norm_sub_rev] at h
    exact h
  have hrle : ‖r‖ < 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hv ht]
  have htpos : 0 < t := by linarith
  have him : t * |(c * v).im| ≤ ‖(t : ℂ) * v - r‖ := by
    have h : |(c * ((t : ℂ) * v - r)).im| ≤ ‖(t : ℂ) * v - r‖ := by
      simpa only [norm_mul, hc, one_mul] using
        Complex.abs_im_le_norm (c * ((t : ℂ) * v - r))
    have heq : c * ((t : ℂ) * v - r) =
        (t : ℂ) * (c * v) - (‖r‖ : ℂ) := by rw [mul_sub, ← hcr]; ring
    rw [heq, Complex.sub_im, Complex.ofReal_im, sub_zero,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, abs_mul, abs_of_nonneg ht] at h
    exact h
  nlinarith

/-- A unit rotation and translation turn a bounded strip into a rectangle. -/
theorem volume_rotated_strip (x c : ℂ) (hc : ‖c‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    volume {τ : ℂ | ‖τ - x‖ ≤ 1 ∧ |(c * (τ - x)).im| ≤ 2 * δ} ≤
      ENNReal.ofReal (8 * δ) := by
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    _root_.rotation ⟨c, mem_sphere_zero_iff_norm.mpr hc⟩
  let R : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (-2 * δ) (2 * δ)
  have hmp : MeasurePreserving (fun τ : ℂ =>
      Complex.measurableEquivRealProd (e (τ - x))) volume volume :=
    Complex.volume_preserving_equiv_real_prod.comp
      (e.measurePreserving.comp (measurePreserving_sub_right volume x))
  have hR : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  have hsub : {τ : ℂ | ‖τ - x‖ ≤ 1 ∧ |(c * (τ - x)).im| ≤ 2 * δ} ⊆
      (fun τ : ℂ => Complex.measurableEquivRealProd (e (τ - x))) ⁻¹' R := by
    intro τ hτ
    have hre : |(c * (τ - x)).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (by simpa [norm_mul, hc] using hτ.1)
    refine ⟨abs_le.mp hre, ?_⟩
    change -2 * δ ≤ (c * (τ - x)).im ∧ (c * (τ - x)).im ≤ 2 * δ
    constructor <;> linarith [(abs_le.mp hτ.2).1, (abs_le.mp hτ.2).2]
  calc
    _ ≤ volume ((fun τ : ℂ =>
        Complex.measurableEquivRealProd (e (τ - x))) ⁻¹' R) := measure_mono hsub
    _ = volume R := hmp.measure_preimage hR.nullMeasurableSet
    _ = ENNReal.ofReal (8 * δ) := by
      rw [show volume R = volume (Icc (-1 : ℝ) 1) *
        volume (Icc (-2 * δ) (2 * δ)) by exact Measure.prod_prod _ _,
        Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

/-- The set of detours whose ray passes relatively near one fixed root has
area proportional to the relative error. -/
theorem volume_relative_ray (x r : ℂ) {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    volume {τ : ℂ | ‖τ - x‖ ≤ 1 ∧ ∃ t ∈ Icc (0 : ℝ) 1,
      ‖(t : ℂ) * (τ - x) - (r - x)‖ < δ * ‖r - x‖} ≤
      ENNReal.ofReal (8 * δ) := by
  obtain ⟨c, hc, hcr⟩ := Complex.exists_norm_eq_mul_self (r - x)
  apply (measure_mono (t :=
    {τ : ℂ | ‖τ - x‖ ≤ 1 ∧ |(c * (τ - x)).im| ≤ 2 * δ}) ?_).trans
      (volume_rotated_strip x c hc hδ₀)
  rintro τ ⟨hτ, t, ht, hnear⟩
  exact ⟨hτ, (relative_ray_transverse hc hcr.symm ht.1 hτ hδ hnear).le⟩

/-- Compare root factors to a nonvanishing endpoint, without any lower bound
on the leading coefficient. -/
theorem small_eval_relative_root (q : Polynomial ℂ) (hq : q.natDegree ≤ 2)
    (x s : ℂ) {δ κ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hκ : κ ≤ ‖q.eval x‖) (hsmall : ‖q.eval s‖ < κ * δ ^ 2) :
    ∃ r ∈ q.roots, ‖s - r‖ < δ * ‖x - r‖ := by
  by_contra! h
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ₀).mpr hδ₁
  have hroots : ∀ r ∈ q.roots, ‖x - r‖ ≤ δ⁻¹ * ‖s - r‖ := by
    intro r hr
    have := mul_le_mul_of_nonneg_left (h r hr) (inv_nonneg.mpr hδ₀.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hδ₀.ne', one_mul] using this
  have hcomp := Submission.Lib.K4PolynomialRemez.norm_eval_le_of_root_comparison
    q x s (inv_nonneg.mpr hδ₀.le) hroots
  have hpow : (δ⁻¹) ^ q.natDegree ≤ (δ⁻¹) ^ 2 :=
    pow_le_pow_right₀ hδi hq
  have heq : (δ⁻¹) ^ 2 * (κ * δ ^ 2) = κ := by
    field_simp
  have hlt : ‖q.eval x‖ < κ := calc
    _ ≤ (δ⁻¹) ^ q.natDegree * ‖q.eval s‖ := hcomp
    _ ≤ (δ⁻¹) ^ 2 * ‖q.eval s‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ < (δ⁻¹) ^ 2 * (κ * δ ^ 2) :=
      mul_lt_mul_of_pos_left hsmall (by positivity)
    _ = κ := heq
  exact hlt.not_ge hκ

/-- A univariate quadratic is small somewhere on only a small set of bounded
detour rays, provided its value at their common endpoint is large. -/
theorem volume_ray_small_values (q : Polynomial ℂ) (hq : q.natDegree ≤ 2)
    (x : ℂ) {δ κ : ℝ} (hδ₀ : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hκ : κ ≤ ‖q.eval x‖) :
    volume {τ : ℂ | ‖τ - x‖ ≤ 1 ∧ ∃ t ∈ Icc (0 : ℝ) 1,
      ‖q.eval (x + (t : ℂ) * (τ - x))‖ < κ * δ ^ 2} ≤
      ENNReal.ofReal (16 * δ) := by
  classical
  let S (r : ℂ) : Set ℂ := {τ | ‖τ - x‖ ≤ 1 ∧ ∃ t ∈ Icc (0 : ℝ) 1,
    ‖(t : ℂ) * (τ - x) - (r - x)‖ < δ * ‖r - x‖}
  have hsub : {τ : ℂ | ‖τ - x‖ ≤ 1 ∧ ∃ t ∈ Icc (0 : ℝ) 1,
      ‖q.eval (x + (t : ℂ) * (τ - x))‖ < κ * δ ^ 2} ⊆
      ⋃ r ∈ q.roots.toFinset, S r := by
    rintro τ ⟨hτ, t, ht, hsmall⟩
    obtain ⟨r, hr, hnear⟩ := small_eval_relative_root q hq x
      (x + (t : ℂ) * (τ - x)) hδ₀ (by linarith) hκ hsmall
    have hid : x + (t : ℂ) * (τ - x) - r =
        (t : ℂ) * (τ - x) - (r - x) := by ring
    rw [hid, norm_sub_rev x r] at hnear
    exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr
      ⟨Multiset.mem_toFinset.mpr hr, hτ, t, ht, hnear⟩⟩
  have hcard : (q.roots.toFinset.card : ℝ) ≤ 2 := by
    exact_mod_cast q.roots.toFinset_card_le.trans ((Polynomial.card_roots' q).trans hq)
  calc
    _ ≤ ∑ r ∈ q.roots.toFinset, volume (S r) :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _r ∈ q.roots.toFinset, ENNReal.ofReal (8 * δ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact volume_relative_ray x r hδ₀.le hδ
    _ = ENNReal.ofReal ((q.roots.toFinset.card : ℝ) * (8 * δ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (16 * δ) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith

theorem detour_norms {τ : ℂ} (hτ : τ ∈ closedBall (1 / 2 : ℂ) (1 / 4)) :
    ‖τ‖ ≤ 1 ∧ ‖τ - 1‖ ≤ 1 := by
  have hcenter : ‖τ - (1 / 2 : ℂ)‖ ≤ 1 / 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hτ
  have hh : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  constructor
  · have h := norm_add_le (τ - (1 / 2 : ℂ)) (1 / 2 : ℂ)
    rw [sub_add_cancel, hh] at h
    linarith
  · have h := norm_sub_le (τ - (1 / 2 : ℂ)) (1 / 2 : ℂ)
    have heq : τ - (1 / 2 : ℂ) - 1 / 2 = τ - 1 := by ring
    rw [heq, hh] at h
    linarith

theorem volume_broken_small_values (q : Polynomial ℂ) (hq : q.natDegree ≤ 2)
    {δ κ : ℝ} (hδ₀ : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hκ₀ : κ ≤ ‖q.eval 0‖) (hκ₁ : κ ≤ ‖q.eval 1‖) :
    volume {τ : ℂ | τ ∈ closedBall (1 / 2 : ℂ) (1 / 4) ∧
      ∃ s ∈ segment ℝ (0 : ℂ) τ ∪ segment ℝ τ 1,
        ‖q.eval s‖ < κ * δ ^ 2} ≤ ENNReal.ofReal (32 * δ) := by
  let B (x : ℂ) : Set ℂ := {τ | ‖τ - x‖ ≤ 1 ∧ ∃ t ∈ Icc (0 : ℝ) 1,
    ‖q.eval (x + (t : ℂ) * (τ - x))‖ < κ * δ ^ 2}
  have hsub : {τ : ℂ | τ ∈ closedBall (1 / 2 : ℂ) (1 / 4) ∧
      ∃ s ∈ segment ℝ (0 : ℂ) τ ∪ segment ℝ τ 1,
        ‖q.eval s‖ < κ * δ ^ 2} ⊆ B 0 ∪ B 1 := by
    rintro τ ⟨hτ, s, hs, hsmall⟩
    have hn := detour_norms hτ
    rcases hs with hs | hs
    · obtain ⟨t, ht, rfl⟩ := (segment_eq_image' ℝ (0 : ℂ) τ).symm ▸ hs
      exact Or.inl ⟨by simpa only [sub_zero] using hn.1,
        t, ht, by simpa only [Complex.real_smul] using hsmall⟩
    · rw [segment_symm ℝ τ 1, segment_eq_image'] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact Or.inr ⟨hn.2, t, ht, by simpa only [Complex.real_smul] using hsmall⟩
  calc
    _ ≤ volume (B 0) + volume (B 1) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (16 * δ) + ENNReal.ofReal (16 * δ) :=
      add_le_add (volume_ray_small_values q hq 0 hδ₀ hδ hκ₀)
        (volume_ray_small_values q hq 1 hδ₀ hδ hκ₁)
    _ = ENNReal.ofReal (32 * δ) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Submission.Obl.k4_quadratic_discriminant_safe_paths
