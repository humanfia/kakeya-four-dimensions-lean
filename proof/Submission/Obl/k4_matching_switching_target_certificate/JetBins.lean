-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/JetBins.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Jets

/-!
# Rescaled jets, two-arm jet comparison and jet reconstruction from bins

* `iteratedDeriv_comp_affine`: the iterated derivatives of `s ↦ f (t₀ + c s)` are
  `c^j` times those of `f`, for every function `f` (no smoothness needed).
* `jet_diff_translate`: Taylor translation of the jet gaps of two arms.
* `jet_reconstruct`: the jets on a time interval are determined by approximate
  jets at its center (for instance floor bins), up to the translated bin widths and
  the Taylor remainder.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- Iterated derivatives commute with an affine change of time, for every function. -/
lemma iteratedDeriv_comp_affine (f : ℝ → ℝ) (t₀ c : ℝ) (j : ℕ) :
    iteratedDeriv j (fun s => f (t₀ + c * s)) =
      fun s => c ^ j * iteratedDeriv j f (t₀ + c * s) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [deriv_const_mul_field]
    have h1 := deriv_comp_mul_left c (fun y => iteratedDeriv j f (t₀ + y)) s
    rw [h1, deriv_comp_const_add, iteratedDeriv_succ, smul_eq_mul]
    ring

lemma iteratedDeriv_sub_of_isOpen {f g : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hg : ContDiffOn ℝ n g U) {x : ℝ} (hx : x ∈ U) :
    iteratedDeriv n (f - g) x = iteratedDeriv n f x - iteratedDeriv n g x :=
  iteratedDeriv_sub (hf.contDiffAt (hU.mem_nhds hx)) (hg.contDiffAt (hU.mem_nhds hx))

/-- Taylor translation of the jet gaps of two arms: if at time `t` the order-`k` gaps
are at most `ρ k`, and both top derivatives are bounded by `B` on the segment, then at
`t'` the order-`j` gap is at most the translated gaps plus twice the remainder. -/
theorem jet_diff_translate {f g : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hg : ContDiffOn ℝ n g U) {t t' : ℝ} (hseg : uIcc t t' ⊆ U)
    {B : ℝ} (hBf : ∀ x ∈ uIcc t t', |iteratedDeriv n f x| ≤ B)
    (hBg : ∀ x ∈ uIcc t t', |iteratedDeriv n g x| ≤ B) {ρ : ℕ → ℝ}
    (hρ : ∀ k, k < n → |iteratedDeriv k f t - iteratedDeriv k g t| ≤ ρ k)
    {j : ℕ} (hj : j < n) :
    |iteratedDeriv j f t' - iteratedDeriv j g t'| ≤
      ∑ i ∈ Finset.range (n - j), ρ (j + i) * |t' - t| ^ i / (i.factorial : ℝ)
        + 2 * B * |t' - t| ^ (n - j) / ((n - j).factorial : ℝ) := by
  have ht : t ∈ U := hseg left_mem_uIcc
  have ht' : t' ∈ U := hseg right_mem_uIcc
  have hfg : ContDiffOn ℝ n (f - g) U := hf.sub hg
  have hsub : ∀ k, k ≤ n → ∀ x ∈ U,
      iteratedDeriv k (f - g) x = iteratedDeriv k f x - iteratedDeriv k g x := by
    intro k hk x hx
    exact iteratedDeriv_sub_of_isOpen hU (hf.of_le (by exact_mod_cast hk))
      (hg.of_le (by exact_mod_cast hk)) hx
  have hT := taylor_iteratedDeriv_bound (B := 2 * B) hU hfg hseg (fun x hx => by
    rw [hsub n le_rfl x (hseg hx)]
    calc |iteratedDeriv n f x - iteratedDeriv n g x|
        ≤ |iteratedDeriv n f x| + |iteratedDeriv n g x| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hBf x hx, hBg x hx]) hj
  rw [hsub j hj.le t' ht'] at hT
  have hsum : |∑ i ∈ Finset.range (n - j),
      iteratedDeriv (j + i) (f - g) t * (t' - t) ^ i / (i.factorial : ℝ)| ≤
      ∑ i ∈ Finset.range (n - j), ρ (j + i) * |t' - t| ^ i / (i.factorial : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : j + i < n := by have := Finset.mem_range.mp hi; omega
    rw [hsub (j + i) hi'.le t ht, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    gcongr
    exact hρ (j + i) hi'
  calc |iteratedDeriv j f t' - iteratedDeriv j g t'|
      ≤ |iteratedDeriv j f t' - iteratedDeriv j g t' - ∑ i ∈ Finset.range (n - j),
          iteratedDeriv (j + i) (f - g) t * (t' - t) ^ i / (i.factorial : ℝ)|
        + |∑ i ∈ Finset.range (n - j),
          iteratedDeriv (j + i) (f - g) t * (t' - t) ^ i / (i.factorial : ℝ)| := by
        have := abs_add_le (iteratedDeriv j f t' - iteratedDeriv j g t' -
          ∑ i ∈ Finset.range (n - j),
            iteratedDeriv (j + i) (f - g) t * (t' - t) ^ i / (i.factorial : ℝ))
          (∑ i ∈ Finset.range (n - j),
            iteratedDeriv (j + i) (f - g) t * (t' - t) ^ i / (i.factorial : ℝ))
        simpa using this
    _ ≤ _ := by linarith

/-- Reconstruction of the jets on a segment from approximate jets `a k` at its start
(for instance the centers of floor bins of width `ρ k`). -/
theorem jet_reconstruct {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) {t t' : ℝ} (hseg : uIcc t t' ⊆ U) {B : ℝ}
    (hB : ∀ x ∈ uIcc t t', |iteratedDeriv n f x| ≤ B) {a ρ : ℕ → ℝ}
    (ha : ∀ k, k < n → |iteratedDeriv k f t - a k| ≤ ρ k) {j : ℕ} (hj : j < n) :
    |iteratedDeriv j f t' - ∑ i ∈ Finset.range (n - j), a (j + i) * (t' - t) ^ i /
        (i.factorial : ℝ)| ≤
      ∑ i ∈ Finset.range (n - j), ρ (j + i) * |t' - t| ^ i / (i.factorial : ℝ)
        + B * |t' - t| ^ (n - j) / ((n - j).factorial : ℝ) := by
  have hT := taylor_iteratedDeriv_bound hU hf hseg hB hj
  have hsum : |∑ i ∈ Finset.range (n - j), iteratedDeriv (j + i) f t * (t' - t) ^ i /
        (i.factorial : ℝ) - ∑ i ∈ Finset.range (n - j), a (j + i) * (t' - t) ^ i /
        (i.factorial : ℝ)| ≤
      ∑ i ∈ Finset.range (n - j), ρ (j + i) * |t' - t| ^ i / (i.factorial : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : j + i < n := by have := Finset.mem_range.mp hi; omega
    rw [← sub_div, ← sub_mul, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    gcongr
    exact ha (j + i) hi'
  calc _ = |(iteratedDeriv j f t' - ∑ i ∈ Finset.range (n - j),
          iteratedDeriv (j + i) f t * (t' - t) ^ i / (i.factorial : ℝ))
        + (∑ i ∈ Finset.range (n - j), iteratedDeriv (j + i) f t * (t' - t) ^ i /
          (i.factorial : ℝ) - ∑ i ∈ Finset.range (n - j), a (j + i) * (t' - t) ^ i /
          (i.factorial : ℝ))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- A floor bin of width `w⁻¹` determines a value up to `w⁻¹`. -/
lemma abs_sub_floor_div_le {w y : ℝ} (hw : 0 < w) :
    |y - (Int.floor (w * y) : ℝ) / w| ≤ w⁻¹ := by
  have h1 := Int.floor_le (w * y)
  have h2 := Int.lt_floor_add_one (w * y)
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add, div_le_iff₀ hw]
    rw [add_mul, inv_mul_cancel₀ hw.ne']
    nlinarith
  · rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hw]
    rw [sub_mul, inv_mul_cancel₀ hw.ne']
    nlinarith

/-- Equal floor bins of width `w⁻¹` give values within `w⁻¹`. -/
lemma abs_sub_le_of_floor_eq {w y z : ℝ} (hw : 0 < w)
    (h : Int.floor (w * y) = Int.floor (w * z)) : |y - z| ≤ w⁻¹ := by
  have hy := Int.floor_le (w * y)
  have hy' := Int.lt_floor_add_one (w * y)
  have hz := Int.floor_le (w * z)
  have hz' := Int.lt_floor_add_one (w * z)
  rw [h] at hy hy'
  have hlt : |w * y - w * z| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← mul_sub, abs_mul, abs_of_pos hw] at hlt
  have : |y - z| < w⁻¹ := by
    rw [← one_div, lt_div_iff₀ hw]
    linarith [mul_comm w |y - z|]
  exact this.le

end Submission.Obl.k4_matching_switching_target_certificate
