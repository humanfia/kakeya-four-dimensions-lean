import Mathlib

/-!
# One-dimensional slab estimates for pairs of affine traces

Two affine traces `y₀ + t s` and `y₀' + t s'` on a time interval of length `q` stay
`ε`-close only on a set of times of length at most `min (q, 2ε/|s - s'|)`.  Sorting the
second trace by the smallest dyadic plank around the first one that contains it gives a
bound by a weighted dyadic sum of plank indicators.  This is the pointwise input of the
planar Córdoba collision estimate.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal

/-- An affine function is bounded on an interval iff it is bounded at its endpoints. -/
theorem affine_abs_le_on_Icc_iff (c σ t₀ q w : ℝ) (hq : 0 ≤ q) :
    (∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ w) ↔
      |c + t₀ * σ| ≤ w ∧ |c + (t₀ + q) * σ| ≤ w := by
  constructor
  · intro h
    exact ⟨h t₀ ⟨le_rfl, by linarith⟩, h (t₀ + q) ⟨by linarith, le_rfl⟩⟩
  · rintro ⟨h0, h1⟩ t ht
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · have : t = t₀ := by
        rw [← hq0, add_zero] at ht
        exact le_antisymm ht.2 ht.1
      rw [this]; exact h0
    · set θ := (t - t₀) / q with hθ
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith [ht.1]) hqpos.le
      have hθ1 : θ ≤ 1 := (div_le_one hqpos).mpr (by linarith [ht.2])
      have heq : c + t * σ = (1 - θ) * (c + t₀ * σ) + θ * (c + (t₀ + q) * σ) := by
        rw [hθ]; field_simp; ring_nf
      rw [heq]
      calc |(1 - θ) * (c + t₀ * σ) + θ * (c + (t₀ + q) * σ)|
          ≤ |(1 - θ) * (c + t₀ * σ)| + |θ * (c + (t₀ + q) * σ)| := abs_add_le _ _
        _ = (1 - θ) * |c + t₀ * σ| + θ * |c + (t₀ + q) * σ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
        _ ≤ (1 - θ) * w + θ * w := by gcongr
        _ = w := by ring

/-- The near set of an affine function with nonzero slope is short. -/
theorem volume_affine_near_le (c σ ε : ℝ) (hσ : σ ≠ 0) :
    volume {t : ℝ | |c + t * σ| < ε} ≤ ENNReal.ofReal (2 * ε / |σ|) := by
  have hσ' : 0 < |σ| := abs_pos.mpr hσ
  have hsub : {t : ℝ | |c + t * σ| < ε} ⊆ Icc (-c / σ - ε / |σ|) (-c / σ + ε / |σ|) := by
    intro t ht
    simp only [mem_ofPred_eq] at ht
    have hmul : |t - (-c / σ)| * |σ| < ε := by
      rw [← abs_mul]
      have : (t - -c / σ) * σ = c + t * σ := by field_simp; ring
      rw [this]; exact ht
    have h2 : |t - (-c / σ)| < ε / |σ| := (lt_div_iff₀ hσ').mpr hmul
    rw [abs_lt] at h2
    constructor <;> linarith [h2.1, h2.2]
  calc volume {t : ℝ | |c + t * σ| < ε}
      ≤ volume (Icc (-c / σ - ε / |σ|) (-c / σ + ε / |σ|)) := measure_mono hsub
    _ = ENNReal.ofReal (2 * ε / |σ|) := by rw [Real.volume_Icc]; congr 1; ring

open Classical in
/-- Pointwise dyadic plank bound for the closeness time of two affine traces.  Here
`c + t σ` is the difference of the traces, `|σ| ≤ 2K` and the top plank `2^(n+1) ε`
already contains every trace that comes `ε`-close somewhere on the interval. -/
theorem near_time_le_dyadic_sum (c σ t₀ q ε K : ℝ) (n : ℕ) (hq : 0 < q) (hε : 0 < ε)
    (hσ : |σ| ≤ 2 * K) (htop : ε + 2 * K * q ≤ 2 ^ (n + 1) * ε) :
    volume {t ∈ Icc t₀ (t₀ + q) | |c + t * σ| < ε} ≤
      ∑ i ∈ Finset.range (n + 1),
        if (∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ 2 ^ (i + 1) * ε) then
          ENNReal.ofReal (4 * q / 2 ^ i) else 0 := by
  classical
  by_cases hne : ∃ t ∈ Icc t₀ (t₀ + q), |c + t * σ| < ε
  · obtain ⟨ts, hts, hεs⟩ := hne
    -- every time is within `ε + q |σ|`
    have hfar : ∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ ε + q * |σ| := by
      intro t ht
      have hdist : |t - ts| ≤ q := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hts.1, hts.2]
      calc |c + t * σ| = |(c + ts * σ) + (t - ts) * σ| := by ring_nf
        _ ≤ |c + ts * σ| + |t - ts| * |σ| := by rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ ε + q * |σ| := by gcongr
    have hP : ∃ i, ∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ 2 ^ (i + 1) * ε := by
      refine ⟨n, fun t ht => (hfar t ht).trans ?_⟩
      nlinarith [abs_nonneg σ]
    set i₀ := Nat.find hP with hi₀
    have hi₀spec := Nat.find_spec hP
    have hi₀n : i₀ ≤ n := Nat.find_min' hP (fun t ht => (hfar t ht).trans (by nlinarith [abs_nonneg σ]))
    have hterm : volume {t ∈ Icc t₀ (t₀ + q) | |c + t * σ| < ε} ≤
        ENNReal.ofReal (4 * q / 2 ^ i₀) := by
      rcases Nat.eq_zero_or_pos i₀ with h0 | hpos
      · rw [h0]
        calc volume {t ∈ Icc t₀ (t₀ + q) | |c + t * σ| < ε}
            ≤ volume (Icc t₀ (t₀ + q)) := measure_mono (fun t ht => ht.1)
          _ = ENNReal.ofReal q := by rw [Real.volume_Icc]; congr 1; ring
          _ ≤ ENNReal.ofReal (4 * q / 2 ^ 0) := ENNReal.ofReal_le_ofReal (by norm_num; linarith)
      · obtain ⟨i, hi⟩ : ∃ i, i₀ = i + 1 := ⟨i₀ - 1, by omega⟩
        rw [hi]
        have hnot : ¬ ∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ 2 ^ (i + 1) * ε :=
          Nat.find_min hP (by omega)
        push_neg at hnot
        obtain ⟨t₁, ht₁, hbig⟩ := hnot
        have hdist : |t₁ - ts| ≤ q := by
          rw [abs_le]; constructor <;> linarith [ht₁.1, ht₁.2, hts.1, hts.2]
        have hσq : 2 ^ i * ε < q * |σ| := by
          have h1 : |c + t₁ * σ| ≤ |c + ts * σ| + |t₁ - ts| * |σ| := by
            calc |c + t₁ * σ| = |(c + ts * σ) + (t₁ - ts) * σ| := by ring_nf
              _ ≤ |c + ts * σ| + |t₁ - ts| * |σ| := by rw [← abs_mul]; exact abs_add_le _ _
          have h2 : |t₁ - ts| * |σ| ≤ q * |σ| := by gcongr
          have h3 : (2 : ℝ) ^ (i + 1) * ε = 2 ^ i * ε + 2 ^ i * ε := by ring
          have h4 : ε ≤ 2 ^ i * ε := le_mul_of_one_le_left hε.le (one_le_pow₀ (by norm_num))
          linarith
        have hσpos : 0 < |σ| := by
          by_contra hle
          push_neg at hle
          have : q * |σ| ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hle
          have : 0 < 2 ^ i * ε := by positivity
          linarith
        have hσne : σ ≠ 0 := abs_pos.mp hσpos
        calc volume {t ∈ Icc t₀ (t₀ + q) | |c + t * σ| < ε}
            ≤ volume {t : ℝ | |c + t * σ| < ε} := measure_mono (fun t ht => ht.2)
          _ ≤ ENNReal.ofReal (2 * ε / |σ|) := volume_affine_near_le c σ ε hσne
          _ ≤ ENNReal.ofReal (4 * q / 2 ^ (i + 1)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [div_le_div_iff₀ hσpos (by positivity)]
            have : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
            rw [this]
            nlinarith
    calc volume {t ∈ Icc t₀ (t₀ + q) | |c + t * σ| < ε}
        ≤ ENNReal.ofReal (4 * q / 2 ^ i₀) := hterm
      _ = if (∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ 2 ^ (i₀ + 1) * ε) then
            ENNReal.ofReal (4 * q / 2 ^ i₀) else 0 := by rw [if_pos hi₀spec]
      _ ≤ ∑ i ∈ Finset.range (n + 1),
            if (∀ t ∈ Icc t₀ (t₀ + q), |c + t * σ| ≤ 2 ^ (i + 1) * ε) then
              ENNReal.ofReal (4 * q / 2 ^ i) else 0 :=
        Finset.single_le_sum (f := fun i => if (∀ t ∈ Icc t₀ (t₀ + q),
            |c + t * σ| ≤ 2 ^ (i + 1) * ε) then ENNReal.ofReal (4 * q / 2 ^ i) else 0)
          (fun _ _ => bot_le) (Finset.mem_range.mpr (by omega))
  · push_neg at hne
    have hempty : {t ∈ Icc t₀ (t₀ + q) | |c + t * σ| < ε} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      exact hne t
    rw [hempty, measure_empty]
    exact bot_le

end Submission.Obl.k4_scalar_initial_true_horizon
