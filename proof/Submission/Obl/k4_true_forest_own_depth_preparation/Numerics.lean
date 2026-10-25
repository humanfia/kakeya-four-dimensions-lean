import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Mathlib

/-!
# Numerics of the forest preparation

* `uniform_tail_constant`: finitely many layers' density tails decay with one common exponent.
* `forest_parameters`: one small incoming slack exponent `ρ` makes all losses negligible
  relative to the incoming inverse slack `N ^ (-ρ)`, and leaves room for the output slack
  `N ^ σ` (`2 N ^ ρ ≤ N ^ σ`).
* `forest_numerics`: the exact loss budget of the forest cleanup (`τ = σ / 100`,
  `θ = N ^ (σ / 4)`, `κ = N ^ ρ`) fits in half of the incoming inverse slack.
* `restore_chart_floor`: a retained label keeping half its mass meets the output floor.
-/

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open Filter MeasureTheory Set
open scoped ENNReal

/-- Finitely many eventual power decay estimates hold together with one common exponent. -/
theorem uniform_tail_constant {N : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) {m : ℕ}
    (X : ℕ → ℕ → ℝ≥0∞)
    (htail : ∀ i, i < m → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      X k i ≤ ENNReal.ofReal (N k ^ (-c))) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ k in atTop, ∀ i, i < m →
      X k i ≤ ENNReal.ofReal (N k ^ (-c₀)) := by
  classical
  choose! c hc hev using htail
  let s : Finset ℝ := (Finset.range m).image c ∪ {1}
  have hs : s.Nonempty := ⟨1, by simp [s]⟩
  refine ⟨s.min' hs, ?_, ?_⟩
  · have hmem := s.min'_mem hs
    simp only [s, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hmem
    rcases hmem with ⟨i, hi, heq⟩ | heq
    · rw [← heq]; exact hc i hi
    · rw [heq]; norm_num
  · have hall : ∀ᶠ k in atTop, ∀ i ∈ Finset.range m,
        X k i ≤ ENNReal.ofReal (N k ^ (-c i)) :=
      (Filter.eventually_all_finset _).mpr fun i hi => hev i (Finset.mem_range.mp hi)
    filter_upwards [hall] with k hk i hi
    refine (hk i (Finset.mem_range.mpr hi)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply Real.rpow_le_rpow_of_exponent_le (hN k)
    have hle : s.min' hs ≤ c i :=
      s.min'_le _ (Finset.mem_union_left _ (Finset.mem_image_of_mem c (Finset.mem_range.mpr hi)))
    linarith

/-- One small incoming slack exponent makes the exceptional, list and prior losses
negligible relative to the incoming inverse slack, below the output slack. -/
theorem forest_parameters {N : ℕ → ℝ} (hNt : Tendsto N atTop atTop) {σ τ c₀ K₀ : ℝ}
    (hσ : 0 < σ) (hτ : τ ≤ σ / 2) (hc₀ : 0 < c₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ σ ∧ ∀ᶠ k in atTop,
      2 * N k ^ ρ ≤ N k ^ σ ∧
      K₀ * (N k ^ (-c₀) + N k ^ (5 * ρ + τ - σ)) + N k ^ (-σ) ≤ N k ^ (-ρ) := by
  let ρ := min (σ / 20) (c₀ / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρσ : ρ ≤ σ / 20 := min_le_left _ _
  have hρc : ρ ≤ c₀ / 2 := min_le_right _ _
  refine ⟨ρ, hρ, by linarith, ?_⟩
  have h1 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := -c₀) (b := -ρ) (by linarith) (3 * K₀)
  have h2 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := 5 * ρ + τ - σ) (b := -ρ) (by linarith) (3 * K₀)
  have h3 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := -σ) (b := -ρ) (by linarith) 3
  have h4 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := ρ) (b := σ) (by linarith) 2
  filter_upwards [h1, h2, h3, h4] with k hk1 hk2 hk3 hk4
  refine ⟨hk4.le, ?_⟩
  rw [mul_add]
  have e1 : 3 * K₀ * N k ^ (-c₀) = 3 * (K₀ * N k ^ (-c₀)) := by ring
  have e2 : 3 * K₀ * N k ^ (5 * ρ + τ - σ) = 3 * (K₀ * N k ^ (5 * ρ + τ - σ)) := by ring
  rw [e1] at hk1
  rw [e2] at hk2
  linarith

/-- The slack numerics of the forest cleanup, with `τ = σ / 100`, list threshold
`θ = N ^ (σ / 4)` and incoming slack `κ = N ^ ρ`: all list, exceptional and prior losses of the
`m` layers fit in half of the incoming inverse slack, and the output slack doubles it. -/
theorem forest_numerics {N : ℕ → ℝ} (hNt : Tendsto N atTop atTop) {σ c₀ : ℝ} (m : ℕ)
    (hσ : 0 < σ) (hc₀ : 0 < c₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ σ / 4 ∧ ∀ᶠ k in atTop,
      2 * N k ^ ρ ≤ N k ^ σ ∧
      ((2 + 4 * (m : ℝ)) * (m : ℝ)) *
          (2 * N k ^ (-c₀) + 1024 * (N k ^ ρ) ^ 5 * N k ^ (σ / 100) / N k ^ (σ / 4)) +
        (m : ℝ) * (2 * N k ^ (-c₀) + 256 * (N k ^ ρ) ^ 4 * N k ^ (σ / 100 - σ)) ≤
        (N k ^ ρ)⁻¹ / 2 := by
  let ρ := min (σ / 100) (c₀ / 100)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρσ : ρ ≤ σ / 100 := min_le_left _ _
  have hρc : ρ ≤ c₀ / 100 := min_le_right _ _
  refine ⟨ρ, hρ, by linarith, ?_⟩
  set mm : ℝ := (m : ℝ) with hmm
  have hm0 : 0 ≤ mm := Nat.cast_nonneg m
  have h1 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := -c₀) (b := -ρ) (by linarith) (8 * ((2 + 4 * mm) * mm) * 2)
  have h2 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := 5 * ρ + σ / 100 - σ / 4) (b := -ρ) (by linarith) (8 * ((2 + 4 * mm) * mm) * 1024)
  have h3 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := -c₀) (b := -ρ) (by linarith) (8 * mm * 2)
  have h4 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := 4 * ρ + (σ / 100 - σ)) (b := -ρ) (by linarith) (8 * mm * 256)
  have h5 := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt hNt
    (a := ρ) (b := σ) (by linarith) 2
  filter_upwards [h1, h2, h3, h4, h5, hNt.eventually (eventually_gt_atTop (0 : ℝ))]
    with k hk1 hk2 hk3 hk4 hk5 hN0
  refine ⟨hk5.le, ?_⟩
  set n := N k with hn
  have hpow5 : (n ^ ρ) ^ 5 * n ^ (σ / 100) / n ^ (σ / 4) = n ^ (5 * ρ + σ / 100 - σ / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, ← Real.rpow_sub hN0]
    congr 1
    push_cast
    ring
  have hpow4 : (n ^ ρ) ^ 4 * n ^ (σ / 100 - σ) = n ^ (4 * ρ + (σ / 100 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  have hinv : (n ^ ρ)⁻¹ = n ^ (-ρ) := (Real.rpow_neg hN0.le ρ).symm
  have e1 : 1024 * (n ^ ρ) ^ 5 * n ^ (σ / 100) / n ^ (σ / 4) =
      1024 * n ^ (5 * ρ + σ / 100 - σ / 4) := by
    rw [← hpow5]; ring
  have e2 : 256 * (n ^ ρ) ^ 4 * n ^ (σ / 100 - σ) = 256 * n ^ (4 * ρ + (σ / 100 - σ)) := by
    rw [← hpow4]; ring
  rw [e1, e2, hinv]
  nlinarith [hk1, hk2, hk3, hk4]

/-- Restoring the output floor of a retained label: half of a label's original mass, whose
original floor holds at the incoming slack, meets the floor at a doubled output slack. -/
theorem restore_chart_floor {kin kout a q : ℝ} {m0 m1 : ℝ≥0∞} (hkin : 0 < kin)
    (hdouble : 2 * kin ≤ kout) (ha : 0 ≤ a) (hq : 0 < q)
    (hfloor : ENNReal.ofReal (a / (q * kin)) ≤ m0) (hhalf : m0 ≤ 2 * m1) :
    ENNReal.ofReal (a / (q * kout)) ≤ m1 := by
  have hreal : a / (q * kout) ≤ a / (q * kin) / 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left ha (by positivity)
    nlinarith
  calc ENNReal.ofReal (a / (q * kout)) ≤ ENNReal.ofReal (a / (q * kin) / 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (a / (q * kin)) / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
    _ ≤ m0 / 2 := ENNReal.div_le_div_right hfloor 2
    _ ≤ m1 := by
        apply ENNReal.div_le_of_le_mul
        rw [mul_comm]
        exact hhalf

end Submission.Obl.k4_true_forest_own_depth_preparation
