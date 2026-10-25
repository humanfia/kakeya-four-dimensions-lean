import Submission.Obl.k4_oss_unit_decay.Laws
import Submission.Obl.k4_oss_unit_decay.Numerics

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_oss_unit_decay

/-- Every fixed finite mixing tower preserves a slightly weaker interval exponent,
including the fixed change of scale needed for the Fourier chain. -/
theorem mixing_frostman :
    ∀ m : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ η : ℝ, 0 < η →
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ μ : Fin (m + 2) → Measure ℝ,
    (∀ j, IsProbabilityMeasure (μ j)) →
    (∀ j, μ j (Icc (1 : ℝ) 2)ᶜ = 0) →
    (∀ j x u, δ ≤ u → u ≤ 1 →
      μ j (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) →
    ∀ lam : ℕ → Measure ℝ, lam 0 = halfLaw (μ 0) →
    (∀ k, k < m → lam (k + 1) = mix (lam k) (μ (Fin.ofNat (m + 2) (k + 1)))) →
    (∀ k, k ≤ m → IsProbabilityMeasure (lam k)) ∧
    (∀ k, k ≤ m → lam k (Icc (-1 : ℝ) 1)ᶜ = 0) ∧
    (∀ k, k ≤ m → ∀ x u, δ / (2 * (4 : ℝ) ^ m) ≤ u → u ≤ 1 →
      lam k (Icc (x - u) (x + u)) ≤
        ENNReal.ofReal ((δ / (2 * (4 : ℝ) ^ m)) ^ (-η) * u ^ s)) ∧
    (∀ j x u, δ / (2 * (4 : ℝ) ^ m) ≤ u → u ≤ 1 →
      μ j (Icc (x - u) (x + u)) ≤
        ENNReal.ofReal ((δ / (2 * (4 : ℝ) ^ m)) ^ (-η) * u ^ s)) := by
  intro m s hs hs1 η hη
  let C : ℝ := 2 * 4 ^ m
  have h4 : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨δ₀, hδ₀, hδ₀1, habsorb⟩ :=
    small_absorb (C * C ^ s) (η / 2) η (by linarith)
  refine ⟨η / 2, δ₀, by positivity, hδ₀, ?_⟩
  intro δ hδ hδsmall μ hμprob hμsupp hμcap lam hlam0 hlamstep
  letI : ∀ j, IsProbabilityMeasure (μ j) := hμprob
  have hδ1 : δ ≤ 1 := hδsmall.le.trans hδ₀1
  let A : ℝ := δ ^ (-(η / 2))
  have hA0 : 0 ≤ A := Real.rpow_nonneg hδ.le _
  have hA1 : 1 ≤ A := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hsource : ∀ j, IntervalCap (μ j) δ s A := fun j =>
    intervalCap_of_frostman hA1 hs.le (hμcap j)
  have htower : ∀ k, k ≤ m → IsProbabilityMeasure (lam k) ∧
      lam k (Icc (-1 : ℝ) 1)ᶜ = 0 ∧ IntervalCap (lam k) δ s ((2 * (4 : ℝ) ^ k) * A) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hlam0]
      refine ⟨inferInstance, halfLaw_support (hμsupp 0), ?_⟩
      simpa using intervalCap_halfLaw hδ hs1 hA0 (hsource 0)
    | succ k ih =>
      intro hk
      have hkm : k < m := by omega
      obtain ⟨hprob, hsupp, hcap⟩ := ih (by omega)
      letI : IsProbabilityMeasure (lam k) := hprob
      rw [hlamstep k hkm]
      refine ⟨inferInstance, mix_support hsupp (hμsupp _), ?_⟩
      have hmcap := intervalCap_mix hδ hs1 (by positivity : 0 ≤ (2 * (4 : ℝ) ^ k) * A)
        hcap (hμsupp (Fin.ofNat (m + 2) (k + 1)))
      convert hmcap using 1 <;> rw [pow_succ] <;> ring
  have hd : 0 < δ / C := div_pos hδ hC0
  have hdδ : δ / C ≤ δ := div_le_self hδ.le hC
  have hscale : δ ≤ C * (δ / C) := by
    have he := div_mul_cancel₀ δ hC0.ne'
    nlinarith
  have habs : (C * C ^ s) * A ≤ (δ / C) ^ (-η) :=
    (habsorb δ hδ hδsmall).trans
      (Real.rpow_le_rpow_of_nonpos hd hdδ (by linarith))
  have hCsp : 0 ≤ C ^ s := Real.rpow_nonneg hC0.le _
  have hfinal : ∀ k, k ≤ m → IntervalCap (lam k) (δ / C) s ((δ / C) ^ (-η)) := by
    intro k hk
    have hcap := (htower k hk).2.2.change_scale hd hs.le (by positivity) hC hscale
    apply hcap.mono hd
    calc
      ((2 * (4 : ℝ) ^ k) * A) * C ^ s ≤ (C * C ^ s) * A := by
        have hpow : (4 : ℝ) ^ k ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hk
        dsimp [C]
        nlinarith [mul_nonneg hA0 hCsp,
          mul_le_mul_of_nonneg_right hpow (mul_nonneg hA0 hCsp)]
      _ ≤ _ := habs
  have hsourcefinal : ∀ j, IntervalCap (μ j) (δ / C) s ((δ / C) ^ (-η)) := by
    intro j
    have hcap := (hsource j).change_scale hd hs.le hA0 hC hscale
    apply hcap.mono hd
    calc
      A * C ^ s ≤ (C * C ^ s) * A := by nlinarith [mul_nonneg hA0 hCsp]
      _ ≤ _ := habs
  exact ⟨fun k hk => (htower k hk).1, fun k hk => (htower k hk).2.1,
    fun k hk x u hu _ => hfinal k hk x u hu,
    fun j x u hu _ => hsourcefinal j x u hu⟩

end Submission.Obl.k4_oss_unit_decay
