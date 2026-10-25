import Submission.Obl.k4_general_wide_layer_offset_comparison.Model

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WideScales.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Filter

/-- Choose all three projection depths before any loss or sample. -/
theorem exists_wide_scales {d κ ℓ U L : ℝ} (hd : d < 1) (hκ : 0 < κ)
    (hℓ : 0 < ℓ) (hU : 0 < U) (hL : 2 < L) :
    ∃ s u v : ℝ, 0 < s ∧ L * s < U ∧ 0 < u ∧ u < s ∧
      0 < v ∧ v < u ∧ v < (1 - d) * u / 4 ∧
      (10 / (1 - d) + 3 + ℓ) * u < κ * s := by
  have hLp : 0 < L := by linarith
  obtain ⟨s, hs, hsU⟩ := exists_between (div_pos hU hLp)
  have hLs : L * s < U := by
    have := (lt_div_iff₀ hLp).mp hsU
    nlinarith
  let C := 10 / (1 - d) + 3 + ℓ
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < κ * s / C := div_pos (mul_pos hκ hs) hC
  obtain ⟨u, hu, huupper⟩ := exists_between (lt_min hs hgap)
  have hus : u < s := huupper.trans_le (min_le_left _ _)
  have huC : C * u < κ * s := by
    have hh := (lt_div_iff₀ hC).mp (huupper.trans_le (min_le_right _ _))
    nlinarith
  have hvmax : 0 < min u ((1 - d) * u / 4) := by positivity
  obtain ⟨v, hv, hvupper⟩ := exists_between hvmax
  exact ⟨s, u, v, hs, hLs, hu, hus, hv, hvupper.trans_le (min_le_left _ _),
    hvupper.trans_le (min_le_right _ _), huC⟩

/-- Wide widths at the three depths make a true short block tiny relative
to the common long comparison domain. -/
theorem wide_domain_ratio {N H K q βmin βmax κ ℓ s u : ℝ}
    (hN : 0 < N) (hH : 1 ≤ H) (hK : 0 ≤ K) (hKH : K ≤ H)
    (hq : 0 ≤ q) (hqu : q ≤ K * N ^ (-κ * s))
    (hβlo : N ^ (-ℓ * (s + u)) / H ≤ βmin)
    (hβhi : βmax ≤ H * N ^ (-ℓ * s)) :
    q * N ^ (-ℓ * s) / βmin + q * βmax / βmin ≤
      2 * H ^ 3 * N ^ (-κ * s + ℓ * u) := by
  have hHp : 0 < H := by linarith
  have hlp : 0 < N ^ (-ℓ * (s + u)) / H := by positivity
  have hβp : 0 < βmin := hlp.trans_le hβlo
  have hratio : N ^ (-ℓ * s) / βmin ≤ H * N ^ (ℓ * u) := by
    calc
      _ ≤ N ^ (-ℓ * s) / (N ^ (-ℓ * (s + u)) / H) :=
        div_le_div_of_nonneg_left (by positivity) hlp hβlo
      _ = H * (N ^ (-ℓ * s) / N ^ (-ℓ * (s + u))) := by rw [div_div_eq_mul_div]; ring
      _ = H * N ^ (ℓ * u) := by
        rw [← Real.rpow_sub hN]
        congr 2
        ring
  have hratio2 : βmax / βmin ≤ H ^ 2 * N ^ (ℓ * u) := by
    calc
      _ ≤ (H * N ^ (-ℓ * s)) / βmin := div_le_div_of_nonneg_right hβhi hβp.le
      _ = H * (N ^ (-ℓ * s) / βmin) := by ring
      _ ≤ H * (H * N ^ (ℓ * u)) := mul_le_mul_of_nonneg_left hratio hHp.le
      _ = H ^ 2 * N ^ (ℓ * u) := by ring
  calc
    _ = q * (N ^ (-ℓ * s) / βmin) + q * (βmax / βmin) := by ring
    _ ≤ q * (H * N ^ (ℓ * u)) + q * (H ^ 2 * N ^ (ℓ * u)) :=
      add_le_add (mul_le_mul_of_nonneg_left hratio hq) (mul_le_mul_of_nonneg_left hratio2 hq)
    _ = q * (H + H ^ 2) * N ^ (ℓ * u) := by ring
    _ ≤ (K * N ^ (-κ * s)) * (2 * H ^ 2) * N ^ (ℓ * u) := by
      gcongr
      nlinarith
    _ ≤ (H * N ^ (-κ * s)) * (2 * H ^ 2) * N ^ (ℓ * u) := by gcongr
    _ = 2 * H ^ 3 * N ^ (-κ * s + ℓ * u) := by
      rw [Real.rpow_add hN]
      ring

end Submission.Obl.k4_general_wide_layer_offset_comparison
