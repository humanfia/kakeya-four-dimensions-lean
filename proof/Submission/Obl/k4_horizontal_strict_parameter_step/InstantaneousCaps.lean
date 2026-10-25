import Submission.Lib.K4Homogenization.RetainedDuration

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d50c59d5b1367f287a76eef33f4c400a8e312ee2,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/InstantaneousCaps.lean`.
The namespace and internal imports are changed to o272. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4Homogenization

/-- The density cutoff and a line/time-bin duration floor turn an integrated mixed cap
into an instantaneous cap for the same probability prior. The time length cancels. -/
theorem instantaneous_cap_of_weighted_duration {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (lam : Measure (α × ℝ))
    {G : α × ℝ → ENNReal} (hG : Measurable G)
    {I : Set ℝ} (hI : MeasurableSet I) {C : Set α} (hC : MeasurableSet C)
    (Cplus : Set (α × ℝ))
    (himp : ∀ l ∈ C, ∀ t ∈ I, (l, t) ∈ Cplus)
    {δ τ K B : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hK : 0 < K) (hB : 0 ≤ B)
    (hweighted : ENNReal.ofReal δ • (ν.prod volume).withDensity G ≤ lam)
    (hcap : lam (Cplus ∩ (univ ×ˢ I)) ≤ ENNReal.ofReal (B * τ)) :
    ν (durationRetained volume G I (ENNReal.ofReal (τ / K)) ∩ C) ≤
      ENNReal.ofReal (K * B / δ) := by
  let S := durationRetained volume G I (ENNReal.ofReal (τ / K)) ∩ C
  have hprior := retained_duration_prior_cap ν volume hG hI
    (ENNReal.ofReal (τ / K)) hC Cplus himp
  have hmass : ENNReal.ofReal δ * (ENNReal.ofReal (τ / K) * ν S) ≤ ENNReal.ofReal (B * τ) := by
    calc
      _ ≤ ENNReal.ofReal δ * (ν.prod volume).withDensity G (Cplus ∩ (univ ×ˢ I)) :=
        mul_le_mul_of_nonneg_left hprior (by positivity)
      _ ≤ lam (Cplus ∩ (univ ×ˢ I)) := by
        simpa only [Measure.smul_apply, smul_eq_mul] using hweighted (Cplus ∩ (univ ×ˢ I))
      _ ≤ _ := hcap
  have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hB hτ.le) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
    ENNReal.toReal_ofReal (div_nonneg hτ.le hK.le)] at hreal
  have hcancel : δ * (ν S).toReal ≤ K * B := by
    apply (mul_le_mul_iff_of_pos_right hτ).mp
    calc
      δ * (ν S).toReal * τ = K * (δ * (τ / K * (ν S).toReal)) := by field_simp
      _ ≤ K * (B * τ) := mul_le_mul_of_nonneg_left hreal hK.le
      _ = K * B * τ := by ring
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top ν _) (by positivity)).mpr
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm δ] using hcancel)

/-- A bounded affine speed keeps a tested scalar constraint inside its enlarged time-bin
constraint throughout the same short time interval. -/
theorem affine_constraint_over_interval {a v c t₀ t s τ w V : ℝ}
    (ht₀ : t₀ ∈ Icc s (s + τ)) (ht : t ∈ Icc s (s + τ))
    (hv : |v| ≤ V) (hvalue : |a + t₀ * v - c| ≤ w) :
    |a + t * v - c| ≤ w + V * τ := by
  have hτ : 0 ≤ τ := by linarith [ht.1, ht.2]
  have hV : 0 ≤ V := (abs_nonneg _).trans hv
  have htime : |t - t₀| ≤ τ := abs_le.mpr
    ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
  have heq : a + t * v - c = (a + t₀ * v - c) + (t - t₀) * v := by ring
  rw [heq]
  calc
    |(a + t₀ * v - c) + (t - t₀) * v| ≤ |a + t₀ * v - c| + |(t - t₀) * v| := abs_add_le _ _
    _ ≤ w + τ * V := add_le_add hvalue (by rw [abs_mul]; exact mul_le_mul htime hv (abs_nonneg _) hτ)
    _ = w + V * τ := by ring

end Submission.Obl.k4_horizontal_strict_parameter_step
