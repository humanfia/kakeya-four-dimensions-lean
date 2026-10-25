import Submission.Obl.k4_scalar_noisy_block_packets.CommonBlock

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open Submission.Obl.k4_scalar_noisy_block_packets
  (blockLeft blockLength blockInterval blockInterval_eq blockLeft_nonneg blockRight_le_one)

abbrev Trajectory := ℕ × (Fin 5 → ℝ)
abbrev Incidence := Trajectory × ℝ

noncomputable def scalarY (l : Trajectory) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

noncomputable def scalarX (l : Trajectory) (t : ℝ) : ℝ :=
  l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

noncomputable def packetOrigin (T : ℕ) (j : Fin (2 ^ T)) (u v : ℝ) : Fin 2 → ℝ :=
  ![blockLeft T j, u + blockLeft T j * v]

noncomputable def normalizedBase (h : ℝ) (z₀ : Fin 2 → ℝ)
    (p : Incidence) : Fin 2 → ℝ :=
  fun e => ((![p.2, scalarY p.1 p.2] : Fin 2 → ℝ) e - z₀ e) / h

theorem blockLength_pos (T : ℕ) : 0 < blockLength T := by
  unfold blockLength
  positivity

theorem blockLength_le_one (T : ℕ) : blockLength T ≤ 1 := by
  unfold blockLength
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

/-- The original dyadic packet has a bounded origin without a velocity shear. -/
theorem packetOrigin_abs_le {K u v : ℝ} (hK : 1 ≤ K) (huv : |u| + |v| ≤ K)
    (T : ℕ) (j : Fin (2 ^ T)) : ∀ e, |packetOrigin T j u v e| ≤ K := by
  have hleft := blockLeft_nonneg T j
  have hright := blockRight_le_one T j
  have hh := (blockLength_pos T).le
  have hleft1 : blockLeft T j ≤ 1 := by linarith
  intro e
  fin_cases e
  · simpa [packetOrigin, abs_of_nonneg hleft] using hleft1.trans hK
  · change |u + blockLeft T j * v| ≤ K
    calc
      |u + blockLeft T j * v| ≤ |u| + |blockLeft T j * v| := abs_add_le _ _
      _ ≤ |u| + |v| := by
        rw [abs_mul, abs_of_nonneg hleft]
        gcongr
        exact mul_le_of_le_one_left (abs_nonneg v) hleft1
      _ ≤ K := huv

/-- Normalizing a packet about its left endpoint costs only a constant in the loss. -/
theorem normalizedBase_abs_le {K u v : ℝ} (hK : 1 ≤ K)
    (huv : |u| + |v| ≤ K) (T : ℕ) (j : Fin (2 ^ T))
    {l : Trajectory} {t : ℝ} (ht : t ∈ blockInterval T j)
    (hy : |scalarY l t - u - t * v| ≤ K / (2 : ℝ) ^ T) :
    ∀ e, |normalizedBase (blockLength T) (packetOrigin T j u v) (l, t) e| ≤ 2 * K := by
  have hh := blockLength_pos T
  have htime : |t - blockLeft T j| ≤ blockLength T := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hv : |v| ≤ K := by linarith [abs_nonneg u]
  have hy' : |scalarY l t - u - t * v| ≤ K * blockLength T := by
    simpa only [div_eq_mul_inv, blockLength] using hy
  intro e
  fin_cases e
  · change |(t - blockLeft T j) / blockLength T| ≤ 2 * K
    rw [abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).mpr (by nlinarith)
  · change |(scalarY l t - (u + blockLeft T j * v)) / blockLength T| ≤ 2 * K
    rw [abs_div, abs_of_pos hh]
    apply (div_le_iff₀ hh).mpr
    calc
      |scalarY l t - (u + blockLeft T j * v)| =
          |(scalarY l t - u - t * v) + (t - blockLeft T j) * v| := by ring_nf
      _ ≤ |scalarY l t - u - t * v| + |(t - blockLeft T j) * v| := abs_add_le _ _
      _ ≤ K * blockLength T + blockLength T * K := by
        rw [abs_mul]
        exact add_le_add hy' (mul_le_mul htime hv (abs_nonneg v) hh.le)
      _ = 2 * K * blockLength T := by ring

/-- Dyadic horizons retain the exact real-power scale of the frozen packet data. -/
theorem blockLength_comparison {N K κ : ℝ} (hN : 0 < N) (hK : 0 < K) (T : ℕ)
    (hlo : N ^ κ / K ≤ (2 : ℝ) ^ T)
    (hhi : (2 : ℝ) ^ T ≤ K * N ^ κ) :
    N ^ (-κ) / K ≤ blockLength T ∧ blockLength T ≤ K * N ^ (-κ) := by
  have hpow : 0 < N ^ κ := Real.rpow_pos_of_pos hN _
  have htwo : 0 < (2 : ℝ) ^ T := by positivity
  rw [Real.rpow_neg hN.le]
  unfold blockLength
  constructor
  · simp only [inv_eq_one_div]
    apply (le_div_iff₀ htwo).mpr
    have : (2 : ℝ) ^ T / (K * N ^ κ) ≤ 1 := (div_le_one (by positivity)).mpr hhi
    convert this using 1 <;> field_simp
  · simp only [inv_eq_one_div]
    apply (div_le_iff₀ htwo).mpr
    have hscale : N ^ κ ≤ (2 : ℝ) ^ T * K := (div_le_iff₀ hK).mp hlo
    have hdiv : 1 ≤ (K * (2 : ℝ) ^ T) / N ^ κ := by
      apply (le_div_iff₀ hpow).mpr
      nlinarith [hscale]
    convert hdiv using 1 <;> field_simp

end Submission.Obl.k4_scalar_grid_cartesian_field
