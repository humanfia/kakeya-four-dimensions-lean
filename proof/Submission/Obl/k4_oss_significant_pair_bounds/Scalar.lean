import Submission.Lib.K4WeightedCellEnergy
import Submission.Obl.k4_oss_unit_decay.Numerics

namespace Submission.Obl.k4_oss_significant_pair_bounds

/-- The mass and size estimates from the weighted energy bound, together with
its sharper comparison of the two cardinalities. -/
theorem scalar_bounds {p q N M Z θ : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hN : 0 < N) (hM : 0 < M)
    (hZ : 0 < Z) (hθ : 0 < θ)
    (hpMass : p * N ≤ 1) (hqMass : q * M ≤ 1)
    (hpSq : p ^ 2 * N ≤ Z) (hqSq : q ^ 2 * M ≤ Z)
    (henergy : θ * Z ≤ 129 * (p ^ 2 * N) * (q ^ 2 * M) * min N M) :
    θ / 129 ≤ (p * N) ^ 2 ∧ N ≤ 129 / (θ * Z) ∧ θ * N ≤ 129 * M := by
  obtain ⟨hmass, hlow, hhigh⟩ :=
    Submission.Lib.K4WeightedCellEnergy.large_pair_forces_mass_and_size
      hp hq hN hM hZ (by norm_num : (0 : ℝ) < 129) hθ
      hpMass hqMass hpSq hqSq henergy
  refine ⟨hmass, by simpa using hhigh, ?_⟩
  have hp2 : (p * N) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (mul_nonneg hp hN.le) hpMass 2
  apply (mul_le_mul_iff_left₀ hZ).mp
  calc
    θ * N * Z = (θ * Z) * N := by ring
    _ ≤ (129 * (p ^ 2 * N) * (q ^ 2 * M) * min N M) * N :=
      mul_le_mul_of_nonneg_right henergy hN.le
    _ ≤ (129 * (p ^ 2 * N) * Z * M) * N := by
      gcongr
      exact min_le_right N M
    _ = 129 * (p * N) ^ 2 * M * Z := by ring
    _ ≤ 129 * 1 * M * Z := by gcongr
    _ = (129 * M) * Z := by ring

/-- Absorb the absolute counting constants in the three available exponent gaps. -/
theorem exists_cutoff {γ a : ℝ} (ha : 0 < a) (hγa : 8 * a < γ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      129 * δ ^ (2 * a) ≤ 1 ∧
      387 * δ ^ (-(1 - γ + 2 * a)) ≤ δ ^ (-(1 - γ / 2)) ∧
      129 * δ ^ (-(2 * a)) ≤ δ ^ (-(3 * a)) := by
  obtain ⟨r₁, hr₁, hr₁1, h₁⟩ :=
    Submission.Obl.k4_oss_unit_decay.small_rpow_bound 129 (2 * a) (by linarith)
  obtain ⟨r₂, hr₂, hr₂1, h₂⟩ :=
    Submission.Obl.k4_oss_unit_decay.small_absorb 387 (1 - γ + 2 * a) (1 - γ / 2)
      (by linarith)
  obtain ⟨r₃, hr₃, hr₃1, h₃⟩ :=
    Submission.Obl.k4_oss_unit_decay.small_absorb 129 (2 * a) (3 * a) (by linarith)
  refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃),
    (min_le_left _ _).trans hr₁1, ?_⟩
  intro δ hδ hδr
  have hd₁ : δ < r₁ := hδr.trans_le (min_le_left _ _)
  have hd₂ : δ < r₂ := hδr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd₃ : δ < r₃ := hδr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨h₁ δ hδ hd₁, h₂ δ hδ hd₂, h₃ δ hδ hd₃⟩

/-- Scalar exclusions at a sufficiently small scale, for one of the two levels. -/
theorem power_bounds {γ a δ p q N M Z : ℝ} (hδ : 0 < δ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hN : 0 < N) (hM : 0 < M) (hZ : 0 < Z)
    (hpMass : p * N ≤ 1) (hqMass : q * M ≤ 1)
    (hpSq : p ^ 2 * N ≤ Z) (hqSq : q ^ 2 * M ≤ Z)
    (hZlower : δ ^ (1 - γ) / 3 ≤ Z)
    (hsmall : 129 * δ ^ (2 * a) ≤ 1)
    (hcap : 387 * δ ^ (-(1 - γ + 2 * a)) ≤ δ ^ (-(1 - γ / 2)))
    (hratio : 129 * δ ^ (-(2 * a)) ≤ δ ^ (-(3 * a)))
    (henergy : δ ^ (2 * a) * Z ≤ 129 * (p ^ 2 * N) * (q ^ 2 * M) * min N M) :
    δ ^ (2 * a) ≤ p * N ∧ N ≤ δ ^ (-1 + γ / 2) ∧ N ≤ δ ^ (-3 * a) * M := by
  have hθ : 0 < δ ^ (2 * a) := Real.rpow_pos_of_pos hδ _
  obtain ⟨hmass, hhigh, hbalance⟩ :=
    scalar_bounds hp hq hN hM hZ hθ hpMass hqMass hpSq hqSq henergy
  refine ⟨?_, ?_, ?_⟩
  · have hm : 0 ≤ p * N := mul_nonneg hp hN.le
    have hsq : (δ ^ (2 * a)) ^ 2 ≤ δ ^ (2 * a) / 129 := by
      nlinarith only [mul_le_mul_of_nonneg_right hsmall hθ.le]
    exact (sq_le_sq₀ hθ.le hm).mp (hsq.trans hmass)
  · calc
      N ≤ 129 / (δ ^ (2 * a) * Z) := hhigh
      _ ≤ 129 / (δ ^ (2 * a) * (δ ^ (1 - γ) / 3)) := by gcongr
      _ = 387 * δ ^ (-(1 - γ + 2 * a)) := by
        rw [Real.rpow_neg hδ.le, ← one_div,
          show 1 - γ + 2 * a = 2 * a + (1 - γ) by ring,
          Real.rpow_add hδ]
        field_simp
        ring
      _ ≤ δ ^ (-(1 - γ / 2)) := hcap
      _ = δ ^ (-1 + γ / 2) := by congr 1; ring
  · have hdiv : N ≤ (129 / δ ^ (2 * a)) * M := by
      calc
        N ≤ (129 * M) / δ ^ (2 * a) :=
          (le_div_iff₀ hθ).mpr (by nlinarith only [hbalance])
        _ = (129 / δ ^ (2 * a)) * M := by ring
    calc
      N ≤ (129 / δ ^ (2 * a)) * M := hdiv
      _ = (129 * δ ^ (-(2 * a))) * M := by rw [Real.rpow_neg hδ.le]; ring
      _ ≤ δ ^ (-(3 * a)) * M := mul_le_mul_of_nonneg_right hratio hM.le
      _ = δ ^ (-3 * a) * M := by congr 2; ring

end Submission.Obl.k4_oss_significant_pair_bounds
