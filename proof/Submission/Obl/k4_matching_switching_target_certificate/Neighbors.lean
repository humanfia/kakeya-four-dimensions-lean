-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/Neighbors.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.JetBins
import Submission.Obl.k4_matching_switching_target_certificate.JetScales

/-!
# The two arms of a retained event are neighbors at every record level

At a retained event the two arms have value gap at most `N^(-1+ε)` and `j`-th
derivative gaps at most `N^(-β j + ε)`. At any time within `N^(-r(a))` of the event
time, Taylor translation (`a02:translated-bin-width` of the paper) shows that their
`j`-th derivatives differ by at most `5 N^ε N^(-l_j(a))`, where `r` and `l` are the
jet radius and accuracy of the frozen children.
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

lemma rpow_mul_pow_le {N x y : ℝ} (hN : 1 ≤ N) (i : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ N ^ (-y)) : N ^ (-x) * ρ ^ i ≤ N ^ (-(x + (i : ℝ) * y)) := by
  have hN0 : 0 < N := by linarith
  calc N ^ (-x) * ρ ^ i ≤ N ^ (-x) * (N ^ (-y)) ^ i := by
        gcongr
    _ = N ^ (-(x + (i : ℝ) * y)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
        congr 1; ring

/-- **Neighbor bins.** The two arms of a retained event have `j`-th derivatives within
`5 N^ε N^(-l_j(a))` at every time within `N^(-r(a))` of the event time. -/
theorem arm_gap_at_level {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {N ε : ℝ} (hN : 1 ≤ N)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hg : ContDiffOn ℝ (J + 1 : ℕ) g (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ N ^ ε)
    (hgB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) g t| ≤ N ^ ε)
    {t c : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
    (h0 : |f t - g t| ≤ N ^ (-1 + ε))
    (hgap : ∀ j : ℕ, 1 ≤ j → j ≤ J →
      |iteratedDeriv j f t - iteratedDeriv j g t| ≤ N ^ (-β j + ε))
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hdist : |c - t| ≤ N ^ (-jetRadius J β a))
    {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j f c - iteratedDeriv j g c| ≤
      5 * N ^ ε * N ^ (-jetAccuracy (jetRadius J β) j a) := by
  have hN0 : 0 < N := by linarith
  set r := jetRadius J β with hr_def
  set l := jetAccuracy r with hl_def
  have hrc : Continuous r := continuous_jetRadius hJ β
  have hrm : Monotone r := monotone_jetRadius hJ β
  have hNε : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 ε
  -- the gap bounds `ρ`
  set ρ : ℕ → ℝ := fun i => if i = 0 then N ^ (-1 + ε) else N ^ (-β i + ε) with hρ_def
  have hρ : ∀ i, i < J + 1 → |iteratedDeriv i f t - iteratedDeriv i g t| ≤ ρ i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa [hρ_def] using h0
    · have : ρ i = N ^ (-β i + ε) := by simp only [hρ_def]; rw [if_neg (by omega)]
      rw [this]
      exact hgap i hi0 (by omega)
  have hseg : uIcc t c ⊆ Ioo (-1 : ℝ) 2 := fun x hx =>
    let h := uIcc_subset_Icc ht hc hx
    ⟨by linarith [h.1], by linarith [h.2]⟩
  have hT := jet_diff_translate isOpen_Ioo hf hg hseg
    (fun x hx => hfB x (uIcc_subset_Icc ht hc hx))
    (fun x hx => hgB x (uIcc_subset_Icc ht hc hx)) hρ (by omega : j < J + 1)
  have hd0 : 0 ≤ |c - t| := abs_nonneg _
  -- each translated gap is at most `N^ε N^(-l_j(a))`
  have hterm : ∀ i ∈ Finset.range (J + 1 - j),
      ρ (j + i) * |c - t| ^ i / (i.factorial : ℝ) ≤
        N ^ ε * N ^ (-l j a) * (1 / (i.factorial : ℝ)) := by
    intro i hi
    have hi' : j + i ≤ J := by have := Finset.mem_range.mp hi; omega
    have key : ρ (j + i) * |c - t| ^ i ≤ N ^ ε * N ^ (-l j a) := by
      rcases Nat.eq_zero_or_pos (j + i) with h0' | hpos
      · have hj0 : j = 0 := by omega
        have hi0 : i = 0 := by omega
        subst hj0; subst hi0
        have hρ0 : ρ (0 + 0) = N ^ (-1 + ε) := by simp [hρ_def]
        rw [hρ0, pow_zero, mul_one, show l 0 a = a from jetAccuracy_zero_order hrc ha,
          ← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      · have hρi : ρ (j + i) = N ^ (-β (j + i) + ε) := by
          simp only [hρ_def]; rw [if_neg (by omega)]
        rw [hρi]
        have h1 : N ^ (-β (j + i) + ε) * |c - t| ^ i ≤
            N ^ ε * N ^ (-(β (j + i) + (i : ℝ) * r a)) := by
          rw [show -β (j + i) + ε = ε + -β (j + i) by ring, Real.rpow_add hN0, mul_assoc]
          exact mul_le_mul_of_nonneg_left (rpow_mul_pow_le hN i hd0 hdist) hNε.le
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hNε.le)
        refine Real.rpow_le_rpow_of_exponent_le hN ?_
        have htr := jetAccuracy_translation hrc hrm j i ha
        have hb := jetAccuracy_le_beta (J := J) β ha hpos hi'
        linarith
    calc ρ (j + i) * |c - t| ^ i / (i.factorial : ℝ)
        = (ρ (j + i) * |c - t| ^ i) * (1 / (i.factorial : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right key (by positivity)
  have hsum : ∑ i ∈ Finset.range (J + 1 - j), ρ (j + i) * |c - t| ^ i / (i.factorial : ℝ)
      ≤ 3 * (N ^ ε * N ^ (-l j a)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have he : ∑ i ∈ Finset.range (J + 1 - j), 1 / (i.factorial : ℝ) ≤ 3 := by
      have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (J + 1 - j)
      have h2 := Real.exp_one_lt_d9
      simp only [one_pow] at h1
      linarith
    have hpos : 0 ≤ N ^ ε * N ^ (-l j a) := by positivity
    nlinarith
  have hrem : 2 * N ^ ε * |c - t| ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ) ≤
      2 * (N ^ ε * N ^ (-l j a)) := by
    have hfac : (1 : ℝ) ≤ ((J + 1 - j).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : |c - t| ^ (J + 1 - j) ≤ N ^ (-l j a) := by
      have h1 : |c - t| ^ (J + 1 - j) ≤ N ^ (-(0 + ((J + 1 - j : ℕ) : ℝ) * r a)) := by
        have := rpow_mul_pow_le (x := 0) hN (J + 1 - j) hd0 hdist
        simpa using this
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
      have hrem := jetAccuracy_le_remainder hJ β hk hkJ hβk ha hj
      have hcast : ((J + 1 - j : ℕ) : ℝ) = (J : ℝ) + 1 - (j : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      linarith
    calc 2 * N ^ ε * |c - t| ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ)
        ≤ 2 * N ^ ε * |c - t| ^ (J + 1 - j) := div_le_self (by positivity) hfac
      _ ≤ 2 * N ^ ε * N ^ (-l j a) := by gcongr
      _ = 2 * (N ^ ε * N ^ (-l j a)) := by ring
  calc |iteratedDeriv j f c - iteratedDeriv j g c| ≤ _ := hT
    _ ≤ 3 * (N ^ ε * N ^ (-l j a)) + 2 * (N ^ ε * N ^ (-l j a)) := by
        have := add_le_add hsum hrem
        simpa [mul_comm, mul_assoc, mul_left_comm] using this
    _ = 5 * N ^ ε * N ^ (-l j a) := by ring

end Submission.Obl.k4_matching_switching_target_certificate
