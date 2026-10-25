-- Adapted from this LOT tree, o114, session x0680, branch x0680,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/BandInterpolation.lean.

import Submission.Obl.k4_tempered_grid_selection.Exponents
import Submission.Obl.k4_quadratic_atlas_normalization.PowerBins

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Band

open Set

/-- Caps at finitely many fixed depths imply a band cap for every width.
`F` may be an original-law band mass over any fixed base set and center. -/
theorem band_bound_of_depth_grid {N L u d A : ℝ} {V : ENNReal}
    (hN : 1 < N) (hL : 0 ≤ L) (hu : 0 ≤ u) (hd : 0 ≤ d) (hA : 0 ≤ A)
    (R : Finset ℝ) (hLmem : L ∈ R)
    (hcover : ∀ r ∈ Icc 0 L, ∃ s ∈ R, s ≤ r ∧ r ≤ s + u)
    (F : ℝ → ENNReal) (hmono : Monotone F)
    (hgrid : ∀ r ∈ R, F (N ^ (-r)) ≤ ENNReal.ofReal (A * N ^ (d * (L - r))) * V)
    (hwhole : ∀ ρ, F ρ ≤ ENNReal.ofReal (A * N ^ (d * L)) * V)
    {ρ : ℝ} (hρ : 0 < ρ) :
    F ρ ≤ ENNReal.ofReal
      (A * N ^ (d * u) * (max ρ (N ^ (-L)) / N ^ (-L)) ^ d) * V := by
  have hN0 : 0 < N := by linarith
  have hδ : 0 < N ^ (-L) := Real.rpow_pos_of_pos hN0 _
  have hdu : 1 ≤ N ^ (d * u) := Real.one_le_rpow hN.le (mul_nonneg hd hu)
  by_cases hsmall : ρ ≤ N ^ (-L)
  · have hcap := (hmono hsmall).trans (hgrid L hLmem)
    have hfactor : A * N ^ (d * (L - L)) ≤
        A * N ^ (d * u) * (max ρ (N ^ (-L)) / N ^ (-L)) ^ d := by
      rw [max_eq_right hsmall, div_self hδ.ne', Real.one_rpow, mul_one,
        sub_self, mul_zero, Real.rpow_zero, mul_one]
      nlinarith
    exact hcap.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) le_rfl)
  · have hδρ : N ^ (-L) ≤ ρ := (lt_of_not_ge hsmall).le
    rw [max_eq_left hδρ]
    by_cases hlarge : 1 ≤ ρ
    · have hratio : N ^ L ≤ ρ / N ^ (-L) := by
        rw [Real.rpow_neg hN0.le, div_inv_eq_mul]
        nlinarith [Real.rpow_nonneg hN0.le L]
      have hpow : N ^ (d * L) ≤ (ρ / N ^ (-L)) ^ d := by
        rw [mul_comm d L, Real.rpow_mul hN0.le]
        exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hratio hd
      apply (hwhole ρ).trans
      apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hx : 0 ≤ (ρ / N ^ (-L)) ^ d := Real.rpow_nonneg (by positivity) _
      have hAdu : A ≤ A * N ^ (d * u) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hdu hA
      exact (mul_le_mul_of_nonneg_left hpow hA).trans
        (mul_le_mul_of_nonneg_right hAdu hx)
    · let r := Submission.Obl.k4_tempered_grid_selection.logarithmicExponent N ρ
      have hrpow : N ^ (-r) = ρ :=
        Submission.Obl.k4_tempered_grid_selection.rpow_neg_logarithmicExponent hN hρ
      have hr0 : 0 ≤ r := by
        have hx : N ^ (-r) ≤ N ^ (0 : ℝ) := by rw [hrpow, Real.rpow_zero]; linarith
        have := (Real.rpow_le_rpow_left_iff hN).mp hx
        linarith
      have hrL : r ≤ L := by
        have hx : N ^ (-L) ≤ N ^ (-r) := by rwa [hrpow]
        have := (Real.rpow_le_rpow_left_iff hN).mp hx
        linarith
      obtain ⟨s, hs, hsr, hrs⟩ := hcover r ⟨hr0, hrL⟩
      have hρs : ρ ≤ N ^ (-s) := by
        rw [← hrpow]
        exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      have hratio : (ρ / N ^ (-L)) ^ d = N ^ ((L - r) * d) := by
        rw [← hrpow, ← Real.rpow_sub hN0, ← Real.rpow_mul hN0.le]
        congr 1
        ring
      have hexp : d * (L - s) ≤ d * u + (L - r) * d := by nlinarith
      have hpow : N ^ (d * (L - s)) ≤ N ^ (d * u) * (ρ / N ^ (-L)) ^ d := by
        rw [hratio, ← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN.le hexp
      apply ((hmono hρs).trans (hgrid s hs)).trans
      apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      calc A * N ^ (d * (L - s)) ≤ A * (N ^ (d * u) * (ρ / N ^ (-L)) ^ d) :=
          mul_le_mul_of_nonneg_left hpow hA
        _ = _ := by ring

/-- Comparable positive terminal widths give comparable band ratios. -/
lemma band_ratio_le_two {ρ α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβα : β ≤ 2 * α) :
    max ρ α / α ≤ 2 * (max ρ β / β) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hrat : β / α ≤ 2 := (div_le_iff₀ hα).mpr hβα
  calc max ρ α / α ≤ max ρ β / α :=
      div_le_div_of_nonneg_right (max_le_max_left ρ hαβ) hα.le
    _ = (β / α) * (max ρ β / β) := by field_simp
    _ ≤ 2 * (max ρ β / β) :=
      mul_le_mul_of_nonneg_right hrat (div_nonneg ((hβ.le).trans (le_max_right _ _)) hβ.le)

/-- The all-width band estimate in the dyadically rounded terminal width,
with any larger cap exponent. -/
theorem band_bound_of_comparable_depth_grid {N L u d dc A δ : ℝ} {V : ENNReal}
    (hN : 1 < N) (hL : 0 ≤ L) (hu : 0 ≤ u) (hd : 0 ≤ d) (hdc : d ≤ dc) (hA : 0 ≤ A)
    (hδlow : N ^ (-L) ≤ δ) (hδupp : δ ≤ 2 * N ^ (-L))
    (R : Finset ℝ) (hLmem : L ∈ R)
    (hcover : ∀ r ∈ Icc 0 L, ∃ s ∈ R, s ≤ r ∧ r ≤ s + u)
    (F : ℝ → ENNReal) (hmono : Monotone F)
    (hgrid : ∀ r ∈ R, F (N ^ (-r)) ≤ ENNReal.ofReal (A * N ^ (d * (L - r))) * V)
    (hwhole : ∀ ρ, F ρ ≤ ENNReal.ofReal (A * N ^ (d * L)) * V)
    {ρ : ℝ} (hρ : 0 < ρ) :
    F ρ ≤ ENNReal.ofReal
      (A * (2 : ℝ) ^ d * N ^ (d * u) * (max ρ δ / δ) ^ dc) * V := by
  have hN0 : 0 < N := by linarith
  have hδ₀ : 0 < N ^ (-L) := Real.rpow_pos_of_pos hN0 _
  have hδ : 0 < δ := hδ₀.trans_le hδlow
  have hrat := band_ratio_le_two (ρ := ρ) hδ₀ hδlow hδupp
  have hβ : 0 ≤ max ρ δ / δ := div_nonneg ((hδ.le).trans (le_max_right _ _)) hδ.le
  have hβ1 : 1 ≤ max ρ δ / δ := (le_div_iff₀ hδ).mpr (by simp)
  have hpow : (max ρ (N ^ (-L)) / N ^ (-L)) ^ d ≤
      (2 : ℝ) ^ d * (max ρ δ / δ) ^ dc := by
    calc (max ρ (N ^ (-L)) / N ^ (-L)) ^ d ≤ (2 * (max ρ δ / δ)) ^ d :=
        Real.rpow_le_rpow (by positivity) hrat hd
      _ = (2 : ℝ) ^ d * (max ρ δ / δ) ^ d := Real.mul_rpow (by norm_num) hβ
      _ ≤ (2 : ℝ) ^ d * (max ρ δ / δ) ^ dc :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hβ1 hdc) (by positivity)
  apply (band_bound_of_depth_grid hN hL hu hd hA R hLmem hcover F hmono hgrid hwhole hρ).trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc A * N ^ (d * u) * (max ρ (N ^ (-L)) / N ^ (-L)) ^ d ≤
      A * N ^ (d * u) * ((2 : ℝ) ^ d * (max ρ δ / δ) ^ dc) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring


end Submission.Obl.k4_compatible_pair_frame_preparation.Band
