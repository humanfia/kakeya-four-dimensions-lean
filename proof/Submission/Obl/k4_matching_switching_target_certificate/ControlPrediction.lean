import Submission.Obl.k4_matching_switching_target_certificate.LevelTranslate

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set

/-- Translation from a refined active-order bin and the higher bins at the reference level.
The active-order error gains the palette exponent `b`; every other error gains the margin. -/
theorem control_prediction_error_bound {J m : ℕ} (hmJ : m ≤ J) {β : ℕ → ℝ}
    {N B K γ b a : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hγ0 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - β m)
    (hγ : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ B)
    {tz t : ℝ} (htz : tz ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hdist : |t - tz| ≤ N ^ (-jetRadius J β a)) (A : ℕ → ℝ)
    (hA0 : |iteratedDeriv m f tz - A m| ≤ N ^ (-(β m + b)))
    (hA : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) f tz - A (m + i)| ≤
        K * N ^ (-jetAccuracy (jetRadius J β) (m + i) a)) :
    |N ^ β m * (iteratedDeriv m f t - ∑ i ∈ Finset.range (J + 1 - m),
        A (m + i) * (t - tz) ^ i / (i.factorial : ℝ))| ≤
      N ^ (-b) + (3 * K + B) * N ^ (-γ) := by
  have hN0 : 0 < N := by linarith
  have hW : 0 < N ^ β m := Real.rpow_pos_of_pos hN0 _
  have hseg : uIcc tz t ⊆ Ioo (-1 : ℝ) 2 := fun x hx =>
    let h := uIcc_subset_Icc htz ht hx
    ⟨by linarith [h.1], by linarith [h.2]⟩
  have hrec := jet_reconstruct (ρ := fun i => |iteratedDeriv i f tz - A i|)
    isOpen_Ioo hf hseg (fun x hx => hfB x (uIcc_subset_Icc htz ht hx))
    (fun _ _ => le_rfl) (by omega : m < J + 1)
  obtain ⟨k, hk⟩ : ∃ k, J + 1 - m = k + 1 := ⟨J - m, by omega⟩
  have hzero : N ^ β m * |iteratedDeriv m f tz - A m| ≤ N ^ (-b) := by
    calc _ ≤ N ^ β m * N ^ (-(β m + b)) := mul_le_mul_of_nonneg_left hA0 hW.le
      _ = N ^ (-b) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hterm : ∀ i ∈ Finset.range k,
      N ^ β m * (|iteratedDeriv (m + (i + 1)) f tz - A (m + (i + 1))| *
        |t - tz| ^ (i + 1) / ((i + 1).factorial : ℝ)) ≤
      K * N ^ (-γ) * (1 / ((i + 1).factorial : ℝ)) := by
    intro i hi
    have hiJ : m + (i + 1) ≤ J := by have := Finset.mem_range.mp hi; omega
    have hp : |t - tz| ^ (i + 1) ≤
        N ^ (-(((i + 1 : ℕ) : ℝ) * jetRadius J β a)) := by
      have := rpow_mul_pow_le (x := 0) hN (i + 1) (abs_nonneg _) hdist
      simpa only [neg_zero, Real.rpow_zero, one_mul, zero_add] using this
    have he : N ^ β m *
        (N ^ (-jetAccuracy (jetRadius J β) (m + (i + 1)) a) *
          N ^ (-(((i + 1 : ℕ) : ℝ) * jetRadius J β a))) ≤ N ^ (-γ) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      apply Real.rpow_le_rpow_of_exponent_le hN
      have := hγ (i + 1) (by omega) hiJ
      linarith
    calc N ^ β m * (|iteratedDeriv (m + (i + 1)) f tz - A (m + (i + 1))| *
          |t - tz| ^ (i + 1) / ((i + 1).factorial : ℝ))
        ≤ N ^ β m * ((K * N ^ (-jetAccuracy (jetRadius J β) (m + (i + 1)) a)) *
          N ^ (-(((i + 1 : ℕ) : ℝ) * jetRadius J β a)) / ((i + 1).factorial : ℝ)) := by
          gcongr
          exact hA (i + 1) (by omega) hiJ
      _ = K * (N ^ β m * (N ^ (-jetAccuracy (jetRadius J β) (m + (i + 1)) a) *
          N ^ (-(((i + 1 : ℕ) : ℝ) * jetRadius J β a)))) *
          (1 / ((i + 1).factorial : ℝ)) := by ring
      _ ≤ _ := by gcongr
  have hsum : N ^ β m * (∑ i ∈ Finset.range (J + 1 - m),
      |iteratedDeriv (m + i) f tz - A (m + i)| * |t - tz| ^ i / (i.factorial : ℝ)) ≤
      N ^ (-b) + 3 * K * N ^ (-γ) := by
    rw [hk, Finset.sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, add_zero]
    rw [mul_add, Finset.mul_sum]
    have hfac : ∑ i ∈ Finset.range k, 1 / ((i + 1).factorial : ℝ) ≤ 3 := by
      have h1 := Real.sum_le_exp_of_nonneg (x := 1) (by norm_num) (k + 1)
      rw [Finset.sum_range_succ'] at h1
      simp only [one_pow, Nat.factorial_zero, Nat.cast_one, div_one] at h1
      linarith [Real.exp_one_lt_d9]
    have hsum' : (∑ i ∈ Finset.range k, N ^ β m *
        (|iteratedDeriv (m + (i + 1)) f tz - A (m + (i + 1))| * |t - tz| ^ (i + 1) /
          ((i + 1).factorial : ℝ))) ≤ 3 * K * N ^ (-γ) := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.mul_sum]
      calc K * N ^ (-γ) * (∑ i ∈ Finset.range k, 1 / ((i + 1).factorial : ℝ))
          ≤ K * N ^ (-γ) * 3 := mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = _ := by ring
    linarith
  have hrem : N ^ β m * (B * |t - tz| ^ (J + 1 - m) /
      ((J + 1 - m).factorial : ℝ)) ≤ B * N ^ (-γ) := by
    have hfac : (1 : ℝ) ≤ ((J + 1 - m).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hp : |t - tz| ^ (J + 1 - m) ≤
        N ^ (-(((J + 1 - m : ℕ) : ℝ) * jetRadius J β a)) := by
      have := rpow_mul_pow_le (x := 0) hN (J + 1 - m) (abs_nonneg _) hdist
      simpa only [neg_zero, Real.rpow_zero, one_mul, zero_add] using this
    have hcast : ((J + 1 - m : ℕ) : ℝ) = (J : ℝ) + 1 - (m : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    calc N ^ β m * (B * |t - tz| ^ (J + 1 - m) / ((J + 1 - m).factorial : ℝ))
        ≤ N ^ β m * (B * |t - tz| ^ (J + 1 - m)) := by
          gcongr
          exact div_le_self (by positivity) hfac
      _ ≤ N ^ β m * (B * N ^ (-(((J + 1 - m : ℕ) : ℝ) * jetRadius J β a))) := by gcongr
      _ = B * N ^ (β m - ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a) := by
        rw [hcast, show β m - ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a =
          β m + -(((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a) by ring,
          Real.rpow_add hN0]
        ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity)
  rw [abs_mul, abs_of_pos hW]
  calc _ ≤ N ^ β m * ((∑ i ∈ Finset.range (J + 1 - m),
        |iteratedDeriv (m + i) f tz - A (m + i)| * |t - tz| ^ i / (i.factorial : ℝ)) +
        B * |t - tz| ^ (J + 1 - m) / ((J + 1 - m).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hrec hW.le
    _ ≤ N ^ (-b) + 3 * K * N ^ (-γ) + B * N ^ (-γ) := by
      rw [mul_add]
      exact add_le_add hsum hrem
    _ = _ := by ring

theorem control_prediction_error {J m : ℕ} (hmJ : m ≤ J) {β : ℕ → ℝ}
    {N ε K γ b a : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K)
    (hγ0 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - β m)
    (hγ : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hfB : ∀ t ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f t| ≤ N ^ ε)
    {tz t : ℝ} (htz : tz ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hdist : |t - tz| ≤ N ^ (-jetRadius J β a)) (A : ℕ → ℝ)
    (hA0 : |iteratedDeriv m f tz - A m| ≤ N ^ (-(β m + b)))
    (hA : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) f tz - A (m + i)| ≤
        K * N ^ (-jetAccuracy (jetRadius J β) (m + i) a)) :
    |N ^ β m * (iteratedDeriv m f t - ∑ i ∈ Finset.range (J + 1 - m),
        A (m + i) * (t - tz) ^ i / (i.factorial : ℝ))| ≤
      N ^ (-b) + (3 * K + N ^ ε) * N ^ (-γ) := by
  exact control_prediction_error_bound hmJ hN hK (by positivity) hγ0 hγ hf hfB htz ht hdist A hA0 hA

/-- The normalized active derivative gap varies little throughout a reference interval. -/
theorem active_gap_variation {J m : ℕ} (hmJ : m ≤ J) {β : ℕ → ℝ}
    {N ε γ a : ℝ} (hN : 1 ≤ N) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (hγ0 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - β m)
    (hγ : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ (J + 1 : ℕ) f (Ioo (-1 : ℝ) 2))
    (hg : ContDiffOn ℝ (J + 1 : ℕ) g (Ioo (-1 : ℝ) 2))
    (hfB : ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) f x| ≤ N ^ ε)
    (hgB : ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) g x| ≤ N ^ ε)
    {t ta : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hta : ta ∈ Icc (0 : ℝ) 1)
    (hdist : |ta - t| ≤ N ^ (-jetRadius J β a))
    (hgap : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) f t - iteratedDeriv (m + i) g t| ≤ N ^ (-β (m + i) + ε)) :
    |N ^ β m * ((iteratedDeriv m f ta - iteratedDeriv m g ta) -
        (iteratedDeriv m f t - iteratedDeriv m g t))| ≤ 6 * N ^ ε * N ^ (-γ) := by
  have hN0 : 0 < N := by linarith
  have hNe : 1 ≤ N ^ ε := Real.one_le_rpow hN hε
  have hsub : ∀ j : ℕ, j ≤ J + 1 → ∀ x ∈ Icc (0 : ℝ) 1,
      iteratedDeriv j (f - g) x = iteratedDeriv j f x - iteratedDeriv j g x := by
    intro j hj x hx
    exact iteratedDeriv_sub_of_isOpen isOpen_Ioo
      (hf.of_le (by exact_mod_cast hj)) (hg.of_le (by exact_mod_cast hj))
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let A : ℕ → ℝ := fun j => if j = m then iteratedDeriv m (f - g) t else 0
  have hA0 : |iteratedDeriv m (f - g) t - A m| ≤ N ^ (-(β m + γ)) := by
    simp only [A, ite_true, sub_self, abs_zero]
    positivity
  have hA : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) (f - g) t - A (m + i)| ≤
        N ^ ε * N ^ (-jetAccuracy (jetRadius J β) (m + i) a) := by
    intro i hi hiJ
    have hi0 : i ≠ 0 := by omega
    simp only [A, Nat.add_eq_left, hi0, ite_false, sub_zero]
    rw [hsub (m + i) (by omega) t ht]
    refine (hgap i hi hiJ).trans ?_
    rw [show -β (m + i) + ε = ε + -β (m + i) by ring, Real.rpow_add hN0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hN
    have hb := jetAccuracy_le_beta β ha (by omega : 1 ≤ m + i) hiJ
    linarith
  have hB : ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) (f - g) x| ≤ 2 * N ^ ε := by
    intro x hx
    rw [hsub (J + 1) le_rfl x hx]
    exact (abs_sub _ _).trans (by linarith [hfB x hx, hgB x hx])
  have h := control_prediction_error_bound hmJ hN (K := N ^ ε) (by positivity)
    (B := 2 * N ^ ε) (by positivity) hγ0 hγ (hf.sub hg) hB ht hta hdist A hA0 hA
  have hsum : (∑ i ∈ Finset.range (J + 1 - m),
      A (m + i) * (ta - t) ^ i / (i.factorial : ℝ)) = iteratedDeriv m (f - g) t := by
    obtain ⟨k, hk⟩ : ∃ k, J + 1 - m = k + 1 := ⟨J - m, by omega⟩
    rw [hk, Finset.sum_range_succ']
    simp [A]
  rw [hsum] at h
  change |N ^ β m * (iteratedDeriv m (f - g) ta - iteratedDeriv m (f - g) t)| ≤ _ at h
  rw [hsub m (by omega) ta hta, hsub m (by omega) t ht] at h
  refine h.trans ?_
  have hpos : 0 ≤ N ^ (-γ) := by positivity
  nlinarith

end Submission.Obl.k4_matching_switching_target_certificate
