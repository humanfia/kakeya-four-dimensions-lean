-- Adapted from this LOT tree, o040, session x0118, Submission/Obl/k4_matching_refinement_exponent/LevelTranslate.lean.
import Mathlib
import Submission.Obl.k4_matching_switching_target_certificate.Neighbors

/-!
# Taylor translation at a record level

If two arms have `k`-th derivative gaps at most `K N^(-l_k(a))` at a time `t₁`
(for instance equal or neighboring floor bins at the center of a level-`a` interval),
then at any time within `N^(-r(a))` their `j`-th derivative gap is at most
`(3K + 2N^ε) N^(-l_j(a))` (`a02:translated-bin-width` of the paper). The same holds
for one arm against approximate jets (reconstruction from bins).
-/

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- The exponent bookkeeping shared by all Taylor translations at level `a`. -/
lemma level_sum_bound {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {N ε K : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    {a : ℝ} (ha : 0 ≤ a) {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ N ^ (-jetRadius J β a))
    {j : ℕ} (hj : j ≤ J) :
    ∑ i ∈ Finset.range (J + 1 - j),
        K * N ^ (-jetAccuracy (jetRadius J β) (j + i) a) * d ^ i / (i.factorial : ℝ)
      + 2 * N ^ ε * d ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ)
      ≤ (3 * K + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) j a) := by
  have hN0 : 0 < N := by linarith
  set r := jetRadius J β with hr_def
  set l := jetAccuracy r with hl_def
  have hrc : Continuous r := continuous_jetRadius hJ β
  have hrm : Monotone r := monotone_jetRadius hJ β
  have hNε : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 ε
  have hterm : ∀ i ∈ Finset.range (J + 1 - j),
      K * N ^ (-l (j + i) a) * d ^ i / (i.factorial : ℝ) ≤
        K * N ^ (-l j a) * (1 / (i.factorial : ℝ)) := by
    intro i _
    have key : N ^ (-l (j + i) a) * d ^ i ≤ N ^ (-l j a) := by
      refine (rpow_mul_pow_le hN i hd0 hd).trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
      have := jetAccuracy_translation hrc hrm j i ha
      linarith
    calc K * N ^ (-l (j + i) a) * d ^ i / (i.factorial : ℝ)
        = K * (N ^ (-l (j + i) a) * d ^ i) * (1 / (i.factorial : ℝ)) := by ring
      _ ≤ K * N ^ (-l j a) * (1 / (i.factorial : ℝ)) := by gcongr
  have hsum : ∑ i ∈ Finset.range (J + 1 - j),
      K * N ^ (-l (j + i) a) * d ^ i / (i.factorial : ℝ) ≤ 3 * (K * N ^ (-l j a)) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have he : ∑ i ∈ Finset.range (J + 1 - j), 1 / (i.factorial : ℝ) ≤ 3 := by
      have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (J + 1 - j)
      have h2 := Real.exp_one_lt_d9
      simp only [one_pow] at h1
      linarith
    have hpos : 0 ≤ K * N ^ (-l j a) := by positivity
    nlinarith
  have hrem : 2 * N ^ ε * d ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ) ≤
      2 * N ^ ε * N ^ (-l j a) := by
    have hfac : (1 : ℝ) ≤ ((J + 1 - j).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : d ^ (J + 1 - j) ≤ N ^ (-l j a) := by
      have h1 : d ^ (J + 1 - j) ≤ N ^ (-(0 + ((J + 1 - j : ℕ) : ℝ) * r a)) := by
        have := rpow_mul_pow_le (x := 0) hN (J + 1 - j) hd0 hd
        simpa using this
      refine h1.trans (Real.rpow_le_rpow_of_exponent_le hN ?_)
      have hrem := jetAccuracy_le_remainder hJ β hk hkJ hβk ha hj
      have hcast : ((J + 1 - j : ℕ) : ℝ) = (J : ℝ) + 1 - (j : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      linarith
    calc 2 * N ^ ε * d ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ)
        ≤ 2 * N ^ ε * d ^ (J + 1 - j) := div_le_self (by positivity) hfac
      _ ≤ 2 * N ^ ε * N ^ (-l j a) := by gcongr
  calc _ ≤ 3 * (K * N ^ (-l j a)) + 2 * N ^ ε * N ^ (-l j a) := add_le_add hsum hrem
    _ = (3 * K + 2 * N ^ ε) * N ^ (-l j a) := by ring

/-- **Translation at a record level.** Two arms with jet gaps at most `K N^(-l_k(a))` at
`t₁` have `j`-th derivative gap at most `(3K + 2N^ε) N^(-l_j(a))` at every time `t₂ ∈ [0,1]`
within `N^(-r(a))` of `t₁`. -/
theorem gap_translate_at_level {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {N ε K : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hg : ContDiffOn ℝ (J + 1 : ℕ) g (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ N ^ ε)
    (hgB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) g t| ≤ N ^ ε)
    {a : ℝ} (ha : 0 ≤ a) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (ht₂ : t₂ ∈ Icc (0 : ℝ) 1)
    (hgap : ∀ i : ℕ, i ≤ J → |iteratedDeriv i f t₁ - iteratedDeriv i g t₁| ≤
      K * N ^ (-jetAccuracy (jetRadius J β) i a))
    (hdist : |t₂ - t₁| ≤ N ^ (-jetRadius J β a)) {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j f t₂ - iteratedDeriv j g t₂| ≤
      (3 * K + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) j a) := by
  have hseg : uIcc t₁ t₂ ⊆ Ioo (-1 : ℝ) 2 := fun x hx =>
    let h := uIcc_subset_Icc ht₁ ht₂ hx
    ⟨by linarith [h.1], by linarith [h.2]⟩
  have hT := jet_diff_translate (ρ := fun i => K * N ^ (-jetAccuracy (jetRadius J β) i a))
    isOpen_Ioo hf hg hseg
    (fun x hx => hfB x (uIcc_subset_Icc ht₁ ht₂ hx))
    (fun x hx => hgB x (uIcc_subset_Icc ht₁ ht₂ hx))
    (fun i hi => hgap i (by omega)) (by omega : j < J + 1)
  refine hT.trans ?_
  have := level_sum_bound hJ hk hkJ hβk (ε := ε) hN hK ha (abs_nonneg _) hdist hj
  simpa [mul_assoc] using this

/-- **Reconstruction at a record level.** Approximate jets `A i` within `K N^(-l_i(a))`
of the jets of `f` at `t₁` reconstruct the `j`-th derivative at every `t₂ ∈ [0,1]` within
`N^(-r(a))`, up to `(3K + N^ε) N^(-l_j(a))`. -/
theorem jet_reconstruct_at_level {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {N ε K : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ N ^ ε)
    {a : ℝ} (ha : 0 ≤ a) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (ht₂ : t₂ ∈ Icc (0 : ℝ) 1)
    {A : ℕ → ℝ}
    (hA : ∀ i : ℕ, i ≤ J → |iteratedDeriv i f t₁ - A i| ≤
      K * N ^ (-jetAccuracy (jetRadius J β) i a))
    (hdist : |t₂ - t₁| ≤ N ^ (-jetRadius J β a)) {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j f t₂ - ∑ i ∈ Finset.range (J + 1 - j),
        A (j + i) * (t₂ - t₁) ^ i / (i.factorial : ℝ)| ≤
      (3 * K + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) j a) := by
  have hseg : uIcc t₁ t₂ ⊆ Ioo (-1 : ℝ) 2 := fun x hx =>
    let h := uIcc_subset_Icc ht₁ ht₂ hx
    ⟨by linarith [h.1], by linarith [h.2]⟩
  have hT := jet_reconstruct (ρ := fun i => K * N ^ (-jetAccuracy (jetRadius J β) i a))
    isOpen_Ioo hf hseg (fun x hx => hfB x (uIcc_subset_Icc ht₁ ht₂ hx))
    (fun i hi => hA i (by omega)) (by omega : j < J + 1)
  refine hT.trans ?_
  have hN0 : 0 < N := by linarith
  have hNε : 0 ≤ N ^ ε := (Real.rpow_pos_of_pos hN0 ε).le
  have := level_sum_bound hJ hk hkJ hβk (ε := ε) hN hK ha (abs_nonneg _) hdist hj
  have hextra : N ^ ε * |t₂ - t₁| ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ) ≤
      2 * N ^ ε * |t₂ - t₁| ^ (J + 1 - j) / ((J + 1 - j).factorial : ℝ) := by
    gcongr; linarith
  linarith

/-- Equal floor bins at width `N^(-l)` give values within `N^(-l)`. -/
lemma abs_sub_le_of_floor_rpow_eq {N l y z : ℝ} (hN : 0 < N)
    (h : Int.floor (N ^ l * y) = Int.floor (N ^ l * z)) : |y - z| ≤ N ^ (-l) := by
  have := abs_sub_le_of_floor_eq (Real.rpow_pos_of_pos hN l) h
  rwa [← Real.rpow_neg hN.le] at this

/-- A value is within `N^(-l)` of the left end of its floor bin at width `N^(-l)`. -/
lemma abs_sub_floor_rpow_le {N l y : ℝ} (hN : 0 < N) :
    |y - (Int.floor (N ^ l * y) : ℝ) / N ^ l| ≤ N ^ (-l) := by
  have := abs_sub_floor_div_le (y := y) (Real.rpow_pos_of_pos hN l)
  rwa [← Real.rpow_neg hN.le] at this

/-- **Reconstruction from the floor bins of a record level.** The left ends of the floor
bins of `f` at the center `t₁` of a level-`a` interval determine every derivative of order
`j ≤ J` at every `t₂ ∈ [0,1]` within `N^(-r(a))`, up to `(3 + 2N^ε) N^(-l_j(a))`. -/
theorem floor_reconstruct_at_level {J : ℕ} (hJ : 1 ≤ J) {β : ℕ → ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (hβk : β k = 0)
    {N ε : ℝ} (hN : 1 ≤ N)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ N ^ ε)
    {a : ℝ} (ha : 0 ≤ a) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (ht₂ : t₂ ∈ Icc (0 : ℝ) 1)
    (hdist : |t₂ - t₁| ≤ N ^ (-jetRadius J β a)) {j : ℕ} (hj : j ≤ J) :
    |iteratedDeriv j f t₂ - ∑ i ∈ Finset.range (J + 1 - j),
        (Int.floor (N ^ jetAccuracy (jetRadius J β) (j + i) a *
            iteratedDeriv (j + i) f t₁) : ℝ) / N ^ jetAccuracy (jetRadius J β) (j + i) a *
          (t₂ - t₁) ^ i / (i.factorial : ℝ)| ≤
      (3 + 2 * N ^ ε) * N ^ (-jetAccuracy (jetRadius J β) j a) := by
  have hN0 : 0 < N := by linarith
  have := jet_reconstruct_at_level (K := 1) hJ hk hkJ hβk hN zero_le_one hf hfB ha ht₁ ht₂
    (A := fun i => (Int.floor (N ^ jetAccuracy (jetRadius J β) i a *
      iteratedDeriv i f t₁) : ℝ) / N ^ jetAccuracy (jetRadius J β) i a)
    (fun i _ => by rw [one_mul]; exact abs_sub_floor_rpow_le hN0) hdist hj
  simpa using this

end Submission.Obl.k4_matching_switching_target_certificate
