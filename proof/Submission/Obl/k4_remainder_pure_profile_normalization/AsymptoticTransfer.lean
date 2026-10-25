import Submission.Obl.k4_dyadic_crop_typicality.Assembly

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Absorb a uniform logarithmic ratio window into a transported upper tail. -/
theorem upper_tail_of_ratio {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (W : ℕ → ℕ)
    (w : (k : ℕ) → Fin (W k) → ENNReal)
    (μ : (k : ℕ) → Fin (W k) → Measure Ω)
    (d : (k : ℕ) → Fin (W k) → Ω → ENNReal)
    (ratio : (k : ℕ) → Fin (W k) → ℝ) (R : ℕ → ℝ) (α e : ℝ)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, R k ≤ N k ^ ε)
    (hratio : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b, ratio k b ≤ N k ^ (α + ε))
    (old : ℕ → ℝ → ENNReal)
    (hold : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k => old k (N k ^ (-e + ε))))
    (hfinite : ∀ k hi, (∑ b, w k b * μ k b {z | ENNReal.ofReal (ratio k b * hi) < d k b z}) ≤
      ENNReal.ofReal (R k) * old k hi) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall N (fun k => ∑ b, w k b * μ k b
      {z | ENNReal.ofReal (N k ^ (-(e - α) + τ)) < d k b z}) := by
  intro τ hτ
  let ε := τ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  apply (Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower hN hR (hold ε hε)).mono
  filter_upwards [hratio ε hε] with k hk
  refine (Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (measure_mono ?_)).trans
    (hfinite k (N k ^ (-e + ε)))
  intro z hz
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hz
  have hn0 : 0 < N k := by linarith [hN k]
  calc
    ratio k b * N k ^ (-e + ε) ≤ N k ^ (α + ε) * N k ^ (-e + ε) :=
      mul_le_mul_of_nonneg_right (hk b) (Real.rpow_nonneg hn0.le _)
    _ = N k ^ (α + ε + (-e + ε)) := (Real.rpow_add hn0 _ _).symm
    _ ≤ N k ^ (-(e - α) + τ) :=
      Real.rpow_le_rpow_of_exponent_le (hN k) (by dsimp [ε]; linarith)

/-- Absorb a ratio window and a small refinement error into a transported lower tail. -/
theorem lower_tail_of_ratio {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (W : ℕ → ℕ)
    (w : (k : ℕ) → Fin (W k) → ENNReal)
    (μ : (k : ℕ) → Fin (W k) → Measure Ω)
    (d : (k : ℕ) → Fin (W k) → Ω → ENNReal)
    (ratio : (k : ℕ) → Fin (W k) → ℝ) (R : ℕ → ℝ) (α e : ℝ)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, R k ≤ N k ^ ε)
    (hratio : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b, N k ^ (α - ε) ≤ ratio k b)
    (old : ℕ → ℝ → ENNReal)
    (hold : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k => old k (N k ^ (-e - ε))))
    (hfinite : ∀ k lo δ, 0 ≤ δ → (∑ b, w k b * μ k b
      {z | d k b z < ENNReal.ofReal (ratio k b * δ * lo)}) ≤
      ENNReal.ofReal (R k) * (old k lo + ENNReal.ofReal δ)) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall N (fun k => ∑ b, w k b * μ k b
      {z | d k b z < ENNReal.ofReal (N k ^ (-(e - α) - τ))}) := by
  intro τ hτ
  let ε := τ / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have herror : IsPowerSmall N (fun k => ENNReal.ofReal (N k ^ (-ε))) :=
    ⟨ε, hε, Eventually.of_forall fun _ => le_rfl⟩
  apply (Submission.Obl.k4_dyadic_crop_typicality.powerSmall_mul_subpower hN hR
    ((hold ε hε).add hNt herror)).mono
  filter_upwards [hratio ε hε] with k hk
  refine (Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (measure_mono ?_)).trans
    (hfinite k (N k ^ (-e - ε)) (N k ^ (-ε)) (Real.rpow_nonneg (by linarith [hN k]) _))
  intro z hz
  refine lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal ?_)
  have hn0 : 0 < N k := by linarith [hN k]
  calc
    N k ^ (-(e - α) - τ) ≤ N k ^ (α - ε + -ε + (-e - ε)) :=
      Real.rpow_le_rpow_of_exponent_le (hN k) (by dsimp [ε]; linarith)
    _ = N k ^ (α - ε) * N k ^ (-ε) * N k ^ (-e - ε) := by
      rw [Real.rpow_add hn0, Real.rpow_add hn0]
    _ ≤ ratio k b * N k ^ (-ε) * N k ^ (-e - ε) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hk b) (Real.rpow_nonneg hn0.le _)) (Real.rpow_nonneg hn0.le _)

end Submission.Obl.k4_remainder_pure_profile_normalization
