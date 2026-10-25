import Mathlib

/-!
# Bernoulli selection over a finite index type

A finite, measure-free form of independent sampling. The subsets `T` of a finite type `ι`
carry the weights `selWt p T = ∏_{i ∈ T} p i * ∏_{i ∉ T} (1 - p i)`, the probability that
independent Bernoulli(`p i`) choices select exactly `T`; they sum to `1`. Exponential moments
of `#(T ∩ U)` and of `#T` are products (`sum_selWt_mul_prod`), which gives both Chernoff tails.
A union bound over finitely many tests then gives a subset that is large and meets every test
set in at most its threshold (`exists_good_subset`).
-/

namespace Submission.Obl.k4_weighted_convex_tubes

open Finset

section Selection

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability that independent Bernoulli(`p i`) choices select exactly `T`. -/
noncomputable def selWt (p : ι → ℝ) (T : Finset ι) : ℝ :=
  (∏ i ∈ T, p i) * ∏ i ∈ Tᶜ, (1 - p i)

theorem selWt_nonneg {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (T : Finset ι) :
    0 ≤ selWt p T :=
  mul_nonneg (prod_nonneg fun i _ => hp0 i) (prod_nonneg fun i _ => sub_nonneg.2 (hp1 i))

/-- The generating function of the selection. -/
theorem sum_selWt_mul_prod (p a : ι → ℝ) :
    ∑ T : Finset ι, selWt p T * ∏ i ∈ T, a i = ∏ i, (p i * a i + (1 - p i)) := by
  rw [Fintype.prod_add]
  refine sum_congr rfl fun T _ => ?_
  rw [selWt, prod_mul_distrib]
  ring

theorem sum_selWt (p : ι → ℝ) : ∑ T : Finset ι, selWt p T = 1 := by
  have h := sum_selWt_mul_prod p (fun _ => 1)
  simp only [prod_const_one, mul_one, add_sub_cancel, prod_const_one] at h
  exact h

/-- Markov's inequality for the selection. -/
theorem sum_ite_le_sum_mul {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (E : Finset ι → Prop) [DecidablePred E] (g : Finset ι → ℝ) (hg0 : ∀ T, 0 ≤ g T)
    (hg : ∀ T, E T → 1 ≤ g T) :
    ∑ T, (if E T then selWt p T else 0) ≤ ∑ T, selWt p T * g T := by
  refine sum_le_sum fun T _ => ?_
  have hw := selWt_nonneg hp0 hp1 T
  split_ifs with hE
  · nlinarith [hg T hE]
  · exact mul_nonneg hw (hg0 T)

omit [DecidableEq ι] in
/-- A product bound: `∏ (p i * a i + (1 - p i)) ≤ exp (∑ p i * (a i - 1))` when `0 ≤ a i`. -/
theorem prod_le_exp_sum {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    ∏ i, (p i * a i + (1 - p i)) ≤ Real.exp (∑ i, p i * (a i - 1)) := by
  rw [Real.exp_sum]
  refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
  · have := mul_nonneg (hp0 i) (ha i)
    linarith [hp1 i]
  · have := Real.add_one_le_exp (p i * (a i - 1))
    linarith

/-- Upper tail: the selection meets `U` in more than `t` points with probability at most
`exp (-t + 2 ∑_{i ∈ U} p i)`. -/
theorem upper_tail {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (U : Finset ι)
    (t : ℝ) :
    ∑ T, (if t < ((T ∩ U).card : ℝ) then selWt p T else 0)
      ≤ Real.exp (-t + 2 * ∑ i ∈ U, p i) := by
  set a : ι → ℝ := fun i => if i ∈ U then Real.exp 1 else 1 with ha_def
  have ha0 : ∀ i, 0 ≤ a i := fun i => by
    simp only [ha_def]; split_ifs <;> positivity
  have hprod : ∀ T : Finset ι, ∏ i ∈ T, a i = Real.exp ((T ∩ U).card) := by
    intro T
    simp only [ha_def]
    rw [prod_ite_mem, prod_const, ← Real.exp_nat_mul, mul_one]
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  have hsum : ∑ i, p i * (a i - 1) ≤ 2 * ∑ i ∈ U, p i := by
    have hi : ∀ i, p i * (a i - 1) ≤ if i ∈ U then 2 * p i else 0 := by
      intro i
      simp only [ha_def]
      split_ifs with hi
      · nlinarith [hp0 i]
      · simp
    calc ∑ i, p i * (a i - 1) ≤ ∑ i, (if i ∈ U then 2 * p i else 0) :=
          sum_le_sum fun i _ => hi i
      _ = ∑ i ∈ U, 2 * p i := Fintype.sum_ite_mem U _
      _ = 2 * ∑ i ∈ U, p i := (mul_sum _ _ _).symm
  calc ∑ T, (if t < ((T ∩ U).card : ℝ) then selWt p T else 0)
      ≤ ∑ T, selWt p T * (Real.exp (-t) * ∏ i ∈ T, a i) := by
        refine sum_ite_le_sum_mul hp0 hp1 _ _ (fun T => ?_) (fun T hT => ?_)
        · exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _ => ha0 i)
        · rw [hprod, ← Real.exp_add]
          exact Real.one_le_exp (by linarith)
    _ = Real.exp (-t) * ∏ i, (p i * a i + (1 - p i)) := by
        rw [← sum_selWt_mul_prod, mul_sum]
        refine sum_congr rfl fun T _ => ?_
        ring
    _ ≤ Real.exp (-t) * Real.exp (2 * ∑ i ∈ U, p i) := by
        gcongr
        exact (prod_le_exp_sum hp0 hp1 a ha0).trans (Real.exp_le_exp.2 hsum)
    _ = Real.exp (-t + 2 * ∑ i ∈ U, p i) := by rw [Real.exp_add]

/-- Lower tail: the selection has fewer than half the expected number of points with
probability at most `exp (-(∑ p i) / 8)`. -/
theorem lower_tail {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∑ T, (if 2 * (T.card : ℝ) < ∑ i, p i then selWt p T else 0)
      ≤ Real.exp (-(∑ i, p i) / 8) := by
  set S := ∑ i, p i with hS_def
  set b : ι → ℝ := fun _ => Real.exp (-1) with hb_def
  have hb0 : ∀ i, 0 ≤ b i := fun i => (Real.exp_pos _).le
  have hprod : ∀ T : Finset ι, ∏ i ∈ T, b i = Real.exp (-(T.card : ℝ)) := by
    intro T
    simp only [hb_def]
    rw [prod_const, ← Real.exp_nat_mul]
    ring_nf
  have hb : Real.exp (-1) ≤ 3 / 8 := by
    rw [Real.exp_neg]
    have := Real.exp_one_gt_d9
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    linarith
  have hsum : ∑ i, p i * (b i - 1) ≤ -(5 / 8) * S := by
    rw [hS_def, mul_sum]
    refine sum_le_sum fun i _ => ?_
    simp only [hb_def]
    nlinarith [hp0 i]
  calc ∑ T, (if 2 * (T.card : ℝ) < S then selWt p T else 0)
      ≤ ∑ T, selWt p T * (Real.exp (S / 2) * ∏ i ∈ T, b i) := by
        refine sum_ite_le_sum_mul hp0 hp1 _ _ (fun T => ?_) (fun T hT => ?_)
        · exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _ => hb0 i)
        · rw [hprod, ← Real.exp_add]
          exact Real.one_le_exp (by linarith)
    _ = Real.exp (S / 2) * ∏ i, (p i * b i + (1 - p i)) := by
        rw [← sum_selWt_mul_prod, mul_sum]
        refine sum_congr rfl fun T _ => ?_
        ring
    _ ≤ Real.exp (S / 2) * Real.exp (-(5 / 8) * S) := by
        gcongr
        exact (prod_le_exp_sum hp0 hp1 b hb0).trans (Real.exp_le_exp.2 hsum)
    _ = Real.exp (-S / 8) := by
        rw [← Real.exp_add]
        ring_nf

/-- **Bernoulli selection.** Let `p i ∈ [0, 1]` have total mass at least `16`, and let `U h`
(`h : Fin H`) be test sets with thresholds `t h ≥ 0`. If every nonempty test set has mean
`∑_{i ∈ U h} p i ≤ t h / 4` and `4 H ≤ exp (t h / 2)`, then some subset `T` has at least half
the total mass and meets every test set in at most its threshold. -/
theorem exists_good_subset (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hS : 16 ≤ ∑ i, p i) {H : ℕ} (U : Fin H → Finset ι) (t : Fin H → ℝ)
    (ht0 : ∀ h, 0 ≤ t h)
    (ht : ∀ h, (U h).Nonempty →
      4 * ∑ i ∈ U h, p i ≤ t h ∧ 4 * (H : ℝ) ≤ Real.exp (t h / 2)) :
    ∃ T : Finset ι, ∑ i, p i ≤ 2 * T.card ∧ ∀ h, ((T ∩ U h).card : ℝ) ≤ t h := by
  by_contra hcon
  push Not at hcon
  have hbad : ∀ h : Fin H,
      ∑ T, (if t h < ((T ∩ U h).card : ℝ) then selWt p T else 0) ≤ 1 / (4 * H) := by
    intro h
    have hH : (0 : ℝ) < H := Nat.cast_pos.2 (Fin.pos h)
    by_cases hU : (U h).Nonempty
    · obtain ⟨h1, h2⟩ := ht h hU
      calc _ ≤ Real.exp (-t h + 2 * ∑ i ∈ U h, p i) := upper_tail hp0 hp1 _ _
        _ ≤ Real.exp (-(t h / 2)) := Real.exp_le_exp.2 (by linarith)
        _ = 1 / Real.exp (t h / 2) := by rw [Real.exp_neg, one_div]
        _ ≤ 1 / (4 * H) := one_div_le_one_div_of_le (by positivity) h2
    · rw [not_nonempty_iff_eq_empty] at hU
      have : ∀ T : Finset ι, ¬ t h < ((T ∩ U h).card : ℝ) := fun T => by
        rw [hU, inter_empty, card_empty, Nat.cast_zero]
        exact not_lt.2 (ht0 h)
      simp only [this, ite_false, sum_const_zero]
      positivity
  have key : ∀ T : Finset ι, selWt p T ≤
      (if 2 * (T.card : ℝ) < ∑ i, p i then selWt p T else 0)
        + ∑ h, (if t h < ((T ∩ U h).card : ℝ) then selWt p T else 0) := by
    intro T
    have hw := selWt_nonneg hp0 hp1 T
    have hnn : 0 ≤ ∑ h, (if t h < ((T ∩ U h).card : ℝ) then selWt p T else 0) :=
      sum_nonneg fun h _ => by split_ifs <;> linarith
    by_cases hsmall : 2 * (T.card : ℝ) < ∑ i, p i
    · rw [ite_eq_left hsmall]
      linarith
    · rw [ite_eq_right hsmall, zero_add]
      obtain ⟨h, hh⟩ := hcon T (not_lt.1 hsmall)
      calc selWt p T = (if t h < ((T ∩ U h).card : ℝ) then selWt p T else 0) := by
            rw [ite_eq_left hh]
        _ ≤ _ := single_le_sum (f := fun h => if t h < ((T ∩ U h).card : ℝ) then selWt p T
              else 0) (fun h _ => by split_ifs <;> linarith) (mem_univ h)
  have hsum := sum_le_sum fun T (_ : T ∈ (univ : Finset (Finset ι))) => key T
  rw [sum_selWt, sum_add_distrib, sum_comm] at hsum
  have h2 : ∑ h : Fin H, ∑ T, (if t h < ((T ∩ U h).card : ℝ) then selWt p T else 0) ≤ 1 / 4 := by
    calc _ ≤ ∑ _h : Fin H, 1 / (4 * (H : ℝ)) := sum_le_sum fun h _ => hbad h
      _ = (H : ℝ) * (1 / (4 * H)) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ 1 / 4 := by
        rcases Nat.eq_zero_or_pos H with h0 | h0
        · simp [h0]
        · have : (0 : ℝ) < H := Nat.cast_pos.2 h0
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
  have h3 : Real.exp (-(∑ i, p i) / 8) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
  have h4 : Real.exp (-2) ≤ 1 / 3 := by
    rw [Real.exp_neg, ← one_div]
    have := Real.add_one_le_exp 2
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith [lower_tail hp0 hp1]

end Selection

end Submission.Obl.k4_weighted_convex_tubes
