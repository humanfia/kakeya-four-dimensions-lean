import Submission.Obl.k4_horizontal_coefficient_count.Assembly
import Submission.Obl.k4_horizontal_coefficient_count.Output

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The simultaneous frozen output follows from per-depth heavy covers.
Heaviness is measured on the original current law before making the
common restriction, so its total proposed floor budget is summable. -/
theorem layers_from_heavy_families {α : Type*} [MeasurableSpace α]
    {N K d e₀ u ε R c : ℝ} (hN : 0 < N) (hK : 0 ≤ K) {m : ℕ}
    (sH : Fin m → ℝ) (μ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ)
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hmass : ENNReal.ofReal (K⁻¹) ≤ μ univ) (htotal : μ univ ≤ ENNReal.ofReal K)
    (f : (r : Fin m) → PredictorFamily b (N ^ (-e₀)) (N ^ (-u * sH r))
      (N ^ (-sH r)) (N ^ R) (N ^ ε))
    (hf : ∀ r, (f r).Floors π d (N ^ (ε / 2)) μ)
    (herr : ∀ r, μ {p | ∃ i, p.1 ∈ (f r).A i}ᶜ ≤ ENNReal.ofReal (N ^ (-c)))
    (hbudget : N ^ (-ε) + (m : ℝ) * N ^ (-c) +
      (m : ℝ) * K * N ^ (-ε / 2) < K⁻¹) :
    ∃ ρ : Measure (α × ℝ), ρ ≤ μ ∧ ENNReal.ofReal (N ^ (-ε)) ≤ ρ univ ∧
      Layers N d e₀ u ε R sH ρ π b := by
  have hratio : N ^ (ε / 2) / N ^ ε = N ^ (-ε / 2) := by
    rw [← Real.rpow_sub hN]
    congr 1
    ring
  have hthreshold (r : Fin m) :
      (∑ i, (f r).weight π d (N ^ ε) i) ≤ ENNReal.ofReal (K * N ^ (-ε / 2)) := by
    calc
      _ ≤ ENNReal.ofReal (N ^ (ε / 2) / N ^ ε) * μ univ :=
        (f r).final_threshold_budget π d (Real.rpow_pos_of_pos hN _)
          (Real.rpow_pos_of_pos hN _) μ (hf r)
      _ ≤ ENNReal.ofReal (N ^ (ε / 2) / N ^ ε) * ENNReal.ofReal K :=
        mul_le_mul' le_rfl htotal
      _ = ENNReal.ofReal (K * N ^ (-ε / 2)) := by
        rw [hratio, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), mul_comm]
  have herrsum :
      (∑ r, μ {p | ∃ i, p.1 ∈ (f r).A i}ᶜ) ≤ ENNReal.ofReal ((m : ℝ) * N ^ (-c)) := by
    calc
      _ ≤ ∑ _r : Fin m, ENNReal.ofReal (N ^ (-c)) := Finset.sum_le_sum (fun r _ => herr r)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.rpow_nonneg hN.le _)]
        simp [nsmul_eq_mul]
  have hthresholdsum : (∑ r, ∑ i, (f r).weight π d (N ^ ε) i) ≤
      ENNReal.ofReal ((m : ℝ) * K * N ^ (-ε / 2)) := by
    calc
      _ ≤ ∑ _r : Fin m, ENNReal.ofReal (K * N ^ (-ε / 2)) :=
        Finset.sum_le_sum (fun r _ => hthreshold r)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg
          (fun _ _ => mul_nonneg hK (Real.rpow_nonneg hN.le _))]
        simp [nsmul_eq_mul, mul_assoc]
  obtain ⟨ρ, hρ, hbound, g, hg⟩ := predictor_families_common_floors
    μ b (N ^ (-e₀)) (fun r => N ^ (-u * sH r)) (fun r => N ^ (-sH r))
    (N ^ R) (N ^ ε) π d (N ^ ε) f htime
  refine ⟨ρ, hρ, ?_, layers_of_families N d e₀ u ε R sH ρ π b g
    (fun r => (hg r).1) (fun r => (hg r).2)⟩
  have hsmall : ENNReal.ofReal (N ^ (-ε)) +
      (∑ r, μ {p | ∃ i, p.1 ∈ (f r).A i}ᶜ) +
      (∑ r, ∑ i, (f r).weight π d (N ^ ε) i) < ENNReal.ofReal (K⁻¹) := by
    calc
      _ ≤ ENNReal.ofReal (N ^ (-ε)) + ENNReal.ofReal ((m : ℝ) * N ^ (-c)) +
          ENNReal.ofReal ((m : ℝ) * K * N ^ (-ε / 2)) := by
        exact add_le_add (add_le_add le_rfl herrsum) hthresholdsum
      _ = ENNReal.ofReal (N ^ (-ε) + (m : ℝ) * N ^ (-c) +
          (m : ℝ) * K * N ^ (-ε / 2)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
      _ < ENNReal.ofReal (K⁻¹) :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by positivity) hbudget)).mpr hbudget
  exact (lt_of_add_lt_add_right (lt_of_add_lt_add_right
    (hsmall.trans_le (hmass.trans hbound)))).le

end Submission.Obl.k4_horizontal_coefficient_count
