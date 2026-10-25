-- Adapted from this LOT tree, o080/x0305, Submission/Obl/k4_matching_geometric_path_cover/Jitter.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.PathJets
import Submission.Obl.k4_matching_switching_target_certificate.Tubes

/-!
# Jitter of the endpoint polynomial

The frozen endpoint polynomial `endpointMap` is Lipschitz in all its time arguments
jointly (final time and switch times), with a constant that depends only on a bound of
the controls. Finite Taylor sums with bounded coefficients are Lipschitz as well. Hence
a point whose endpoint lies in a tube around moving centers brings every nearby time
tuple into the tube padded by a multiple of the jitter.

The endpoint estimate `endpointMap_snd_sub_le` follows the argument of
`endpointLow_joint_sub_norm_bound` by session x0047 (o015, branch x0047,
`Submission/Obl/k4_two_color_matching/EndpointLipschitz.lean`), rewritten for the
coordinatewise form used here.

Written for o080 by session x0274.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- Powers of bounded numbers are Lipschitz. -/
lemma abs_pow_sub_pow_le_of_abs_le {a b B : ℝ} (hB : 1 ≤ B) (ha : |a| ≤ B) (hb : |b| ≤ B)
    {k n : ℕ} (hkn : k ≤ n) : |a ^ k - b ^ k| ≤ (n : ℝ) * B ^ n * |a - b| := by
  have hmax0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg _)
  have hpow : max |a| |b| ^ (k - 1) ≤ B ^ n :=
    (pow_le_pow_left₀ hmax0 (max_le ha hb) _).trans (pow_le_pow_right₀ hB (by omega))
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  calc |a ^ k - b ^ k| ≤ |a - b| * k * max |a| |b| ^ (k - 1) := abs_pow_sub_pow_le a b k
    _ ≤ |a - b| * n * B ^ n := by
        gcongr
    _ = (n : ℝ) * B ^ n * |a - b| := by ring

/-- A finite Taylor sum with bounded coefficients is Lipschitz on a bounded interval. -/
lemma taylorSum_sub_le (c : ℕ → ℝ) (n : ℕ) {x₀ s t M R : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i, i < n → |c i| ≤ M) (hR : 1 ≤ R) (hs : |s - x₀| ≤ R) (ht : |t - x₀| ≤ R) :
    |∑ i ∈ Finset.range n, c i * (s - x₀) ^ i / (i.factorial : ℝ) -
        ∑ i ∈ Finset.range n, c i * (t - x₀) ^ i / (i.factorial : ℝ)| ≤
      (n : ℝ) * (M * ((n : ℝ) * R ^ n)) * |s - t| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range n,
      |c i * (s - x₀) ^ i / (i.factorial : ℝ) - c i * (t - x₀) ^ i / (i.factorial : ℝ)| ≤
        M * ((n : ℝ) * R ^ n) * |s - t| := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hf : (1 : ℝ) ≤ (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < i.factorial)]
    have hp := abs_pow_sub_pow_le_of_abs_le hR hs ht hin.le
    rw [sub_sub_sub_cancel_right] at hp
    calc |c i| * |(s - x₀) ^ i - (t - x₀) ^ i| / (i.factorial : ℝ)
        ≤ |c i| * |(s - x₀) ^ i - (t - x₀) ^ i| :=
          div_le_self (by positivity) hf
      _ ≤ M * ((n : ℝ) * R ^ n * |s - t|) :=
          mul_le_mul (hM i hin) hp (abs_nonneg _) hM0
      _ = M * ((n : ℝ) * R ^ n) * |s - t| := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring_nf
  exact le_rfl

/-- **Joint variation of the endpoint polynomial**, in all its time arguments. -/
lemma endpointMap_snd_sub_le {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ : ℝ) {K d : ℝ}
    (hK : 0 ≤ K) (hU : ∀ p, |U p| ≤ K) (hs₀ : |s₀| ≤ 1) (x y : ℝ × (Fin m → ℝ))
    (hx : |x.1| ≤ 1 ∧ ∀ p, |x.2 p| ≤ 1) (hy : |y.1| ≤ 1 ∧ ∀ p, |y.2 p| ≤ 1)
    (hd1 : |x.1 - y.1| ≤ d) (hd2 : ∀ p, |x.2 p - y.2 p| ≤ d) (j : Fin m) :
    |(endpointMap m U s₀ x).2 j - (endpointMap m U s₀ y).2 j| ≤
      K * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m * d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hd1
  have hbase (s : ℝ) (hs : |s| ≤ 1) : |s - s₀| ≤ 2 := by
    have h := abs_sub s s₀
    linarith
  have hrun (s t : ℝ) (hs : |s| ≤ 1) (ht : |t| ≤ 1) : |s - t| ≤ 2 := by
    have h := abs_sub s t
    linarith
  set k := (j : ℕ) + 1 with hk_def
  have hkm : k ≤ m := by have := j.isLt; omega
  have hpow₀ : |(x.1 - s₀) ^ k - (y.1 - s₀) ^ k| ≤ (m : ℝ) * 2 ^ m * d := by
    have h := abs_pow_sub_pow_le_of_abs_le (by norm_num) (hbase _ hx.1) (hbase _ hy.1) hkm
    rw [sub_sub_sub_cancel_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left hd1 (by positivity))
  have hpow (p : Fin m) :
      |(x.1 - x.2 p) ^ k - (y.1 - y.2 p) ^ k| ≤ (m : ℝ) * 2 ^ m * (2 * d) := by
    have h := abs_pow_sub_pow_le_of_abs_le (by norm_num) (hrun _ _ hx.1 (hx.2 p))
      (hrun _ _ hy.1 (hy.2 p)) hkm
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have heq : (x.1 - x.2 p) - (y.1 - y.2 p) = (x.1 - y.1) - (x.2 p - y.2 p) := by ring
    rw [heq]
    have := abs_sub (x.1 - y.1) (x.2 p - y.2 p)
    linarith [hd2 p]
  have hw (p : Fin m) : |U p.succ - U p.castSucc| ≤ 2 * K := by
    have h := abs_sub (U p.succ) (U p.castSucc)
    linarith [hU p.succ, hU p.castSucc]
  have hfact : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have heq : (endpointMap m U s₀ x).2 j - (endpointMap m U s₀ y).2 j =
      (U 0 * ((x.1 - s₀) ^ k - (y.1 - s₀) ^ k) +
        ∑ p : Fin m, (U p.succ - U p.castSucc) *
          ((x.1 - x.2 p) ^ k - (y.1 - y.2 p) ^ k)) / (k.factorial : ℝ) := by
    simp only [endpointMap]
    rw [← hk_def, ← sub_div]
    congr 1
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k.factorial : ℝ))]
  calc _ ≤ |U 0 * ((x.1 - s₀) ^ k - (y.1 - s₀) ^ k) +
        ∑ p : Fin m, (U p.succ - U p.castSucc) *
          ((x.1 - x.2 p) ^ k - (y.1 - y.2 p) ^ k)| :=
        div_le_self (abs_nonneg _) hfact
    _ ≤ |U 0| * |(x.1 - s₀) ^ k - (y.1 - s₀) ^ k| +
        ∑ p : Fin m, |U p.succ - U p.castSucc| *
          |(x.1 - x.2 p) ^ k - (y.1 - y.2 p) ^ k| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul]
        refine add_le_add le_rfl ?_
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (fun p : Fin m => (U p.succ - U p.castSucc) *
            ((x.1 - x.2 p) ^ k - (y.1 - y.2 p) ^ k)) Finset.univ
    _ ≤ K * ((m : ℝ) * 2 ^ m * d) +
        ∑ _p : Fin m, (2 * K) * ((m : ℝ) * 2 ^ m * (2 * d)) := by
        refine add_le_add (mul_le_mul (hU 0) hpow₀ (abs_nonneg _) hK) ?_
        refine Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul (hw p) (hpow p) (abs_nonneg _) (by positivity)
    _ = K * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m * d := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Jitter into a padded tube.** If the endpoint at `y` lies within `e j` of the moving
centers at time `y.1 ∈ [lo, hi]`, then the endpoint at every `x` within `δ` of `y`
(coordinatewise) lies in the tube over `[lo - δ, hi + δ]` with half-widths `w j`, as soon
as `w j` absorbs the endpoint and center motion. -/
theorem endpointMap_mem_tube_of_near {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ : ℝ) {K δ L : ℝ}
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hL0 : 0 ≤ L) (hU : ∀ p, |U p| ≤ K) (hs₀ : |s₀| ≤ 1)
    (y : ℝ × (Fin m → ℝ)) (hy : |y.1| ≤ 1 / 2 ∧ ∀ p, |y.2 p| ≤ 1 / 2) (hδ2 : δ ≤ 1 / 2)
    (center : Fin m → ℝ → ℝ) (e w : Fin m → ℝ) {lo hi : ℝ}
    (hc : ∀ j s t, |s| ≤ 1 → |t| ≤ 1 → |center j s - center j t| ≤ L * |s - t|)
    (hy1 : y.1 ∈ Icc lo hi)
    (hyc : ∀ j, |(endpointMap m U s₀ y).2 j - center j y.1| ≤ e j)
    (hw : ∀ j, e j + (K * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m + L) * δ ≤ w j)
    (x : ℝ × (Fin m → ℝ)) (hx1 : |x.1 - y.1| ≤ δ) (hx2 : ∀ p, |x.2 p - y.2 p| ≤ δ) :
    endpointMap m U s₀ x ∈ tube (Icc (lo - δ) (hi + δ)) center w := by
  have hyu : |y.1| ≤ 1 ∧ ∀ p, |y.2 p| ≤ 1 := ⟨by linarith [hy.1], fun p => by linarith [hy.2 p]⟩
  have hxu : |x.1| ≤ 1 ∧ ∀ p, |x.2 p| ≤ 1 := by
    refine ⟨?_, fun p => ?_⟩
    · have := abs_sub_abs_le_abs_sub x.1 y.1
      linarith [hy.1]
    · have := abs_sub_abs_le_abs_sub (x.2 p) (y.2 p)
      linarith [hy.2 p, hx2 p]
  refine ⟨?_, fun j => ?_⟩
  · change x.1 ∈ Icc (lo - δ) (hi + δ)
    have h := abs_le.mp hx1
    exact ⟨by linarith [hy1.1, h.1], by linarith [hy1.2, h.2]⟩
  · change |(endpointMap m U s₀ x).2 j - center j x.1| ≤ w j
    have h1 := endpointMap_snd_sub_le U s₀ hK hU hs₀ x y hxu hyu hx1 hx2 j
    have h2 := hc j x.1 y.1 hxu.1 hyu.1
    have hjump : |center j x.1 - center j y.1| ≤ L * δ :=
      h2.trans (mul_le_mul_of_nonneg_left hx1 hL0)
    have h3 := hyc j
    have h4 := hw j
    calc |(endpointMap m U s₀ x).2 j - center j x.1|
        ≤ |(endpointMap m U s₀ x).2 j - (endpointMap m U s₀ y).2 j| +
          |(endpointMap m U s₀ y).2 j - center j y.1| + |center j y.1 - center j x.1| := by
          have := abs_sub_le ((endpointMap m U s₀ x).2 j) ((endpointMap m U s₀ y).2 j)
            (center j x.1)
          have := abs_sub_le ((endpointMap m U s₀ y).2 j) (center j y.1) (center j x.1)
          linarith
      _ ≤ K * (m : ℝ) * (4 * (m : ℝ) + 1) * 2 ^ m * δ + e j + L * δ := by
          rw [abs_sub_comm (center j y.1)]
          linarith
      _ ≤ w j := by linarith

end Submission.Obl.k4_matching_switching_target_certificate
