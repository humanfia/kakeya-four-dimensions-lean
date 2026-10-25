import Submission.Obl.k4_oss_unit_decay.CollisionGrowth
import Submission.Obl.k4_oss_unit_decay.Numerics

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_oss_unit_decay

lemma collision_recurrence (m : ℕ) (q : ℕ → ℝ≥0∞) (r T L : ℝ≥0∞)
    (hr : r ≤ 1) (hzero : q 0 ≤ 1)
    (hhigh : ∀ k, k < m → T ≤ q k → q (k + 1) ≤ r * q k)
    (hlow : ∀ k, k < m → q k < T → q (k + 1) ≤ L * T) :
    ∀ k, k ≤ m → q k ≤ max (L * T) (r ^ k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact hzero.trans (by simp)
  | succ k ih =>
    intro hk
    have hkm : k < m := by omega
    by_cases h : q k < T
    · exact (hlow k hkm h).trans (le_max_left _ _)
    · calc
        q (k + 1) ≤ r * q k := hhigh k hkm (le_of_not_gt h)
        _ ≤ r * max (L * T) (r ^ k) := by
          gcongr
          exact ih (by omega)
        _ = max (r * (L * T)) (r ^ (k + 1)) := by rw [mul_max]; simp [pow_succ, mul_comm]
        _ ≤ max (L * T) (r ^ (k + 1)) := by
          apply max_le_max _ le_rfl
          calc
            r * (L * T) ≤ 1 * (L * T) := by gcongr
            _ = _ := one_mul _

lemma collision_parameters (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    ∃ m : ℕ, ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      3 * ENNReal.ofReal (δ ^ c) ≤ 1 ∧
      max (39 * ENNReal.ofReal (δ ^ (1 - γ / 2)))
        ((3 * ENNReal.ofReal (δ ^ c)) ^ m) ≤ ENNReal.ofReal (δ ^ (1 - γ)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / c)
  have hcm : 1 ≤ (c / 2) * (m : ℝ) := by
    have hh := (div_lt_iff₀ hc).mp hm
    nlinarith
  obtain ⟨δ₁, hδ₁, hδ₁1, hsmall₁⟩ := small_rpow_bound 3 (c / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hδ₂1, hsmall₂⟩ := small_rpow_bound 39 (γ / 2) (by linarith)
  refine ⟨m, min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left _ _).trans hδ₁1, ?_⟩
  intro δ hδ hδsmall
  have hδ1 : δ ≤ 1 := (hδsmall.trans_le (min_le_left _ _)).le.trans hδ₁1
  have hgain : 3 * δ ^ c ≤ δ ^ (c / 2) := by
    calc
      3 * δ ^ c = (3 * δ ^ (c / 2)) * δ ^ (c / 2) := by
        rw [mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * δ ^ (c / 2) := mul_le_mul_of_nonneg_right
        (hsmall₁ δ hδ (hδsmall.trans_le (min_le_left _ _))) (Real.rpow_nonneg hδ.le _)
      _ = _ := one_mul _
  have hgain1 : 3 * ENNReal.ofReal (δ ^ c) ≤ 1 := by
    have hh : 3 * δ ^ c ≤ 1 := hgain.trans (Real.rpow_le_one hδ.le hδ1 (by linarith))
    simpa [ENNReal.ofReal_mul, show (0 : ℝ) ≤ 3 by norm_num] using ENNReal.ofReal_le_ofReal hh
  refine ⟨hgain1, max_le ?_ ?_⟩
  · have hh : 39 * δ ^ (1 - γ / 2) ≤ δ ^ (1 - γ) := by
      calc
        39 * δ ^ (1 - γ / 2) = (39 * δ ^ (γ / 2)) * δ ^ (1 - γ) := by
          rw [mul_assoc, ← Real.rpow_add hδ]
          congr 2
          ring
        _ ≤ 1 * δ ^ (1 - γ) := mul_le_mul_of_nonneg_right
          (hsmall₂ δ hδ (hδsmall.trans_le (min_le_right _ _))) (Real.rpow_nonneg hδ.le _)
        _ = _ := one_mul _
    simpa [ENNReal.ofReal_mul, show (0 : ℝ) ≤ 39 by norm_num] using ENNReal.ofReal_le_ofReal hh
  · have hh : (3 * δ ^ c) ^ m ≤ δ ^ (1 - γ) := by
      calc
        _ ≤ (δ ^ (c / 2)) ^ m := pow_le_pow_left₀ (by positivity) hgain _
        _ = δ ^ ((c / 2) * (m : ℝ)) := by rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    simpa only [ENNReal.ofReal_pow (by positivity : 0 ≤ 3 * δ ^ c),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hh

def ProjectionFlattening : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∃ c ε δ₀ : ℝ, 0 < c ∧ 0 < ε ∧ 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ α β : Measure ℝ,
    IsProbabilityMeasure α → IsProbabilityMeasure β →
    α (Icc (-1 : ℝ) 1)ᶜ = 0 → β (Icc (1 : ℝ) 2)ᶜ = 0 →
    (∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      α (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) →
    (∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      β (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) →
    ENNReal.ofReal (δ ^ (1 - γ)) ≤ collision δ α →
    projectionCollision δ α β ≤ ENNReal.ofReal (δ ^ c) * collision δ α

/-- Uniform finite iteration of the flattening alternative. -/
theorem collision_iteration (hflatten : ProjectionFlattening) :
    ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∃ m : ℕ, ∃ η r₀ : ℝ, 0 < η ∧ 0 < r₀ ∧
    ∀ r : ℝ, 0 < r → r < r₀ → ∀ μ : Fin (m + 2) → Measure ℝ,
    (∀ j, IsProbabilityMeasure (μ j)) →
    (∀ j, μ j (Icc (1 : ℝ) 2)ᶜ = 0) →
    (∀ j x u, r ≤ u → u ≤ 1 →
      μ j (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-η) * u ^ s)) →
    ∀ ν : ℕ → Measure ℝ,
    (∀ k, k ≤ m → IsProbabilityMeasure (ν k)) →
    (∀ k, k ≤ m → ν k (Icc (-1 : ℝ) 1)ᶜ = 0) →
    (∀ k, k ≤ m → ∀ x u, r ≤ u → u ≤ 1 →
      ν k (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-η) * u ^ s)) →
    (∀ k, k < m → ν (k + 1) = mix (ν k) (μ (Fin.ofNat (m + 2) (k + 1)))) →
    collision r (ν m) ≤ ENNReal.ofReal (r ^ (1 - γ)) := by
  intro s hs hs1 γ hγ hγ1
  obtain ⟨c, ε, δB, hc, hε, hδB, hB⟩ :=
    hflatten s hs hs1 (γ / 2) (by linarith) (by linarith)
  obtain ⟨m, δN, hδN, hδN1, hN⟩ := collision_parameters c γ hc hγ
  refine ⟨m, ε, min δB δN, hε, lt_min hδB hδN, ?_⟩
  intro r hr hrsmall μ hμprob hμsupp hμcap ν hνprob hνsupp hνcap hνstep
  have hrB : r < δB := hrsmall.trans_le (min_le_left _ _)
  have hrN : r < δN := hrsmall.trans_le (min_le_right _ _)
  obtain ⟨hgain, hmax⟩ := hN r hr hrN
  have hq0 : collision r (ν 0) ≤ 1 := by
    letI : IsProbabilityMeasure (ν 0) := hνprob 0 (by omega)
    exact prob_le_one
  have hrec := collision_recurrence m (fun k => collision r (ν k))
    (3 * ENNReal.ofReal (r ^ c)) (ENNReal.ofReal (r ^ (1 - γ / 2))) 39 hgain hq0
  apply (hrec ?_ ?_ m le_rfl).trans hmax
  · intro k hk hhigh
    letI : IsProbabilityMeasure (ν k) := hνprob k (by omega)
    letI : IsProbabilityMeasure (μ (Fin.ofNat (m + 2) (k + 1))) := hμprob _
    have hf := hB r hr hrB (ν k) (μ (Fin.ofNat (m + 2) (k + 1)))
      inferInstance inferInstance (hνsupp k (by omega)) (hμsupp _)
      (hνcap k (by omega)) (hμcap _) hhigh
    calc
      collision r (ν (k + 1)) ≤
          3 * projectionCollision r (ν k) (μ (Fin.ofNat (m + 2) (k + 1))) := by
        rw [hνstep k hk]
        exact Submission.k4_oss_collision_cauchy_schwarz r hr _ _ inferInstance inferInstance _ rfl
      _ ≤ 3 * (ENNReal.ofReal (r ^ c) * collision r (ν k)) := by gcongr
      _ = (3 * ENNReal.ofReal (r ^ c)) * collision r (ν k) := (mul_assoc _ _ _).symm
  · intro k hk hlow
    letI : IsProbabilityMeasure (ν k) := hνprob k (by omega)
    letI : IsProbabilityMeasure (μ (Fin.ofNat (m + 2) (k + 1))) := hμprob _
    calc
      collision r (ν (k + 1)) ≤ 39 * collision r (ν k) := by
        rw [hνstep k hk]
        exact collision_mix_le _ _ hr (hμsupp _)
      _ ≤ 39 * ENNReal.ofReal (r ^ (1 - γ / 2)) := by gcongr

end Submission.Obl.k4_oss_unit_decay
