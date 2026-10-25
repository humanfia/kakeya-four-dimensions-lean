-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/Jets.lean.
import Mathlib

/-!
# Taylor translation of jets with global iterated derivatives

The frozen statement bounds `iteratedDeriv j f` (the global iterated derivative)
of functions that are `C^(J+1)` on an open interval. This file proves the Taylor
translation estimates for such jets, in both time directions, together with the
version for the difference of two functions.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

lemma iteratedDeriv_iteratedDeriv_eq (i j : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv i (iteratedDeriv j f) = iteratedDeriv (i + j) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add]
  rfl

lemma contDiffOn_iteratedDeriv_of_isOpen {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f U) (hU : IsOpen U) {j : ℕ} (hj : j ≤ n) :
    ContDiffOn ℝ ((n - j : ℕ) : WithTop ℕ∞) (iteratedDeriv j f) U := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [iteratedDeriv_succ]
    refine (ih (by omega)).deriv_of_isOpen hU ?_
    have h : n - j = (n - (j + 1)) + 1 := by omega
    rw [h]
    push_cast
    exact le_rfl

/-- Taylor's theorem (Lagrange form) for the `j`-th derivative with global iterated
derivatives: the jet at `t'` is the Taylor translation of the jet at `t`, up to a
remainder given by the top derivative at an intermediate point. Both time
directions are allowed. -/
theorem taylor_iteratedDeriv_lagrange {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) {t t' : ℝ} (hseg : uIcc t t' ⊆ U) {j : ℕ} (hj : j < n) :
    ∃ ξ ∈ uIcc t t', iteratedDeriv j f t' - ∑ i ∈ Finset.range (n - j),
        iteratedDeriv (j + i) f t * (t' - t) ^ i / (i.factorial : ℝ)
      = iteratedDeriv n f ξ * (t' - t) ^ (n - j) / ((n - j).factorial : ℝ) := by
  obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
  rcases eq_or_ne t t' with rfl | htt
  · refine ⟨t, left_mem_uIcc, ?_⟩
    rw [hk, Finset.sum_range_succ']
    simp
  set g := iteratedDeriv j f with hg_def
  have hg : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g U := by
    rw [← hk]; exact contDiffOn_iteratedDeriv_of_isOpen hf hU hj.le
  have huniq : UniqueDiffOn ℝ (uIcc t t') := uniqueDiffOn_Icc (by
    rcases lt_or_gt_of_ne htt with h | h
    · simp [inf_eq_left.mpr h.le, sup_eq_right.mpr h.le, h]
    · simp [inf_eq_right.mpr h.le, sup_eq_left.mpr h.le, h])
  have hgI : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g (uIcc t t') := hg.mono hseg
  have hgk : ContDiffOn ℝ (k : WithTop ℕ∞) g (uIcc t t') :=
    hgI.of_le (by exact_mod_cast Nat.le_succ k)
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k g (uIcc t t')) (uIoo t t') :=
    (hgI.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self k)
      huniq).mono uIoo_subset_uIcc_self
  obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange htt hgk hdiff
  have hat : ∀ (i : ℕ) (y : ℝ), i ≤ k + 1 → y ∈ uIcc t t' →
      iteratedDerivWithin i g (uIcc t t') y = iteratedDeriv i g y := by
    intro i y hi hy
    refine iteratedDerivWithin_eq_iteratedDeriv huniq ?_ hy
    exact ((hg.contDiffAt (hU.mem_nhds (hseg hy))).of_le (by exact_mod_cast hi))
  have ht_mem : t ∈ uIcc t t' := left_mem_uIcc
  rw [taylor_within_apply] at heq
  have hsum : (∑ i ∈ Finset.range (k + 1),
        ((i.factorial : ℝ)⁻¹ * (t' - t) ^ i) • iteratedDerivWithin i g (uIcc t t') t) =
      ∑ i ∈ Finset.range (n - j),
        iteratedDeriv (j + i) f t * (t' - t) ^ i / (i.factorial : ℝ) := by
    rw [hk]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hat i t (by have := Finset.mem_range.mp hi; omega) ht_mem,
      hg_def, iteratedDeriv_iteratedDeriv_eq, add_comm i j, smul_eq_mul]
    ring
  rw [hsum, hat (k + 1) x' le_rfl (uIoo_subset_uIcc_self hx'), hg_def,
    iteratedDeriv_iteratedDeriv_eq] at heq
  refine ⟨x', uIoo_subset_uIcc_self hx', ?_⟩
  have hkj : k + 1 + j = n := by omega
  rw [hg_def, heq, hk, hkj]

/-- Taylor's theorem for the `j`-th derivative with global iterated derivatives:
the jet at `t'` is the Taylor translation of the jet at `t`, up to the remainder
controlled by the top derivative on the segment. Both time directions are allowed. -/
theorem taylor_iteratedDeriv_bound {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) {t t' : ℝ} (hseg : uIcc t t' ⊆ U) {B : ℝ}
    (hB : ∀ x ∈ uIcc t t', |iteratedDeriv n f x| ≤ B) {j : ℕ} (hj : j < n) :
    |iteratedDeriv j f t' - ∑ i ∈ Finset.range (n - j),
        iteratedDeriv (j + i) f t * (t' - t) ^ i / (i.factorial : ℝ)|
      ≤ B * |t' - t| ^ (n - j) / ((n - j).factorial : ℝ) := by
  obtain ⟨ξ, hξ, heq⟩ := taylor_iteratedDeriv_lagrange hU hf hseg hj
  rw [heq, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hB ξ hξ

/-- The constant-control form: if the top derivative stays within `e` of a constant
`u` on the segment, the jet at `t'` is the Taylor translation of the jet at `t` plus
the exact contribution of the constant control `u`, up to `e` times the
corresponding power. -/
theorem taylor_iteratedDeriv_control {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) {t t' : ℝ} (hseg : uIcc t t' ⊆ U) {u e : ℝ}
    (hu : ∀ x ∈ uIcc t t', |iteratedDeriv n f x - u| ≤ e) {j : ℕ} (hj : j < n) :
    |iteratedDeriv j f t' - ∑ i ∈ Finset.range (n - j),
        iteratedDeriv (j + i) f t * (t' - t) ^ i / (i.factorial : ℝ)
        - u * (t' - t) ^ (n - j) / ((n - j).factorial : ℝ)|
      ≤ e * |t' - t| ^ (n - j) / ((n - j).factorial : ℝ) := by
  obtain ⟨ξ, hξ, heq⟩ := taylor_iteratedDeriv_lagrange hU hf hseg hj
  rw [heq, ← sub_div, ← sub_mul, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hu ξ hξ

end Submission.Obl.k4_matching_switching_target_certificate
