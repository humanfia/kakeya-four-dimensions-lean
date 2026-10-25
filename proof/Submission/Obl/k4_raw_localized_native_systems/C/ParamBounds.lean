import Submission.Obl.k4_raw_localized_native_systems.C.Asymptotics

/-
Adapted from this LOT tree, o178, session x0596, `ParamBounds.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Power bounds for the strip parameters

With slack `1 ≤ κ ≤ N^e`, the strip parameters of `OneSample` satisfy

* `6 N^(-w₂) ≤ ρ ≤ 12 N^(2e - w₂ + u)`,
* `2 ≤ KB ≤ 9 κ` (once `ρ ≤ 1`),
* `g H² ≤ CG N^(6e - w₂ + 3u)` and `gC ≤ Cg N^(7e - w₂ + 3u)` with constants depending
  only on `CB`,
* `KB / (g H²) ≤ 14 N^(2e + w₂)`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {N κ w₂ u e : ℝ}

theorem sRho_pos (hN : 1 ≤ N) (hκ : 1 ≤ κ) : 0 < sRho N κ w₂ (δ N u) := by
  unfold sRho
  have hN0 : 0 < N := by linarith
  have := delta_pos N u
  positivity

theorem sRho_le (hN : 1 ≤ N) (hu : 0 ≤ u) (hκ : 1 ≤ κ) :
    sRho N κ w₂ (δ N u) ≤ 12 * κ ^ 2 * N ^ (-w₂ + u) := by
  unfold sRho
  have hN0 : 0 < N := by linarith
  have hd := rpow_neg_le_delta hN hu
  have hdpos : 0 < N ^ (-u) := Real.rpow_pos_of_pos hN0 _
  rw [div_le_iff₀ (delta_pos N u)]
  have heq : N ^ (-w₂ + u) * N ^ (-u) = N ^ (-w₂) := by
    rw [← Real.rpow_add hN0]; ring_nf
  calc 12 * κ ^ 2 * N ^ (-w₂) = 12 * κ ^ 2 * N ^ (-w₂ + u) * N ^ (-u) := by
        rw [mul_assoc (12 * κ ^ 2), heq]
    _ ≤ 12 * κ ^ 2 * N ^ (-w₂ + u) * δ N u := by
        gcongr

theorem sRho_ge (hN : 1 ≤ N) (hu : 0 ≤ u) (hκ : 1 ≤ κ) :
    6 * N ^ (-w₂) ≤ sRho N κ w₂ (δ N u) := by
  unfold sRho
  have hN0 : 0 < N := by linarith
  have hd := delta_le_two_rpow_neg (u := u) hN
  have hNu : N ^ (-u) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hd2 : δ N u ≤ 2 := by linarith
  have hdpos := delta_pos N u
  rw [le_div_iff₀ hdpos]
  have hk2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hw : 0 < N ^ (-w₂) := Real.rpow_pos_of_pos hN0 _
  nlinarith

theorem two_le_sKB (hκ : 0 ≤ κ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 2 ≤ sKB κ ρ := by
  unfold sKB
  have : (0 : ℝ) ≤ (⌈κ⌉₊ : ℝ) := Nat.cast_nonneg _
  linarith

theorem sKB_le (hκ : 1 ≤ κ) {ρ : ℝ} (hρ1 : ρ ≤ 1) : sKB κ ρ ≤ 9 * κ := by
  unfold sKB
  have hc : (⌈κ⌉₊ : ℝ) ≤ κ + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  linarith

theorem sH_le (hN : 1 ≤ N) (hu : 0 ≤ u) (hκ : 1 ≤ κ) {CB : ℕ} {KB : ℝ} (hKB2 : 2 ≤ KB)
    (hKB : KB ≤ 9 * κ) : sH CB KB (δ N u) ≤ (81 * CB + 72) * κ ^ 2 * N ^ u := by
  unfold sH
  have hN0 : 0 < N := by linarith
  have hNu : 1 ≤ N ^ u := Real.one_le_rpow hN hu
  have hd := rpow_neg_le_delta hN hu
  have hdpos := delta_pos N u
  have hinv : 1 / δ N u ≤ N ^ u := by
    rw [div_le_iff₀ hdpos]
    have : N ^ u * N ^ (-u) = 1 := by rw [← Real.rpow_add hN0]; simp
    nlinarith [Real.rpow_pos_of_pos hN0 u]
  have hKB0 : 0 ≤ KB := by linarith
  have h1 : (CB : ℝ) * KB ^ 2 ≤ CB * (81 * κ ^ 2) * N ^ u := by
    have : KB ^ 2 ≤ 81 * κ ^ 2 := by nlinarith
    have hCB0 : (0 : ℝ) ≤ CB := Nat.cast_nonneg _
    calc (CB : ℝ) * KB ^ 2 ≤ CB * (81 * κ ^ 2) := mul_le_mul_of_nonneg_left this hCB0
      _ = CB * (81 * κ ^ 2) * 1 := (mul_one _).symm
      _ ≤ CB * (81 * κ ^ 2) * N ^ u := by gcongr
  have h2 : 8 * KB / δ N u ≤ 72 * κ ^ 2 * N ^ u := by
    have : 8 * KB / δ N u = 8 * KB * (1 / δ N u) := by ring
    rw [this]
    have hk : κ ≤ κ ^ 2 := by nlinarith
    calc 8 * KB * (1 / δ N u) ≤ 8 * (9 * κ) * N ^ u := by
          gcongr
      _ ≤ 72 * κ ^ 2 * N ^ u := by
          have := Real.rpow_pos_of_pos hN0 u
          nlinarith
  nlinarith

/-- The binned width in power form. -/
theorem binWidth_le (hN : 1 ≤ N) (hu : 0 ≤ u) (he : 0 ≤ e) (hκ : 1 ≤ κ) (hκe : κ ≤ N ^ e)
    (CB : ℕ) (hρ1 : sRho N κ w₂ (δ N u) ≤ 1) :
    sRho N κ w₂ (δ N u) / sKB κ (sRho N κ w₂ (δ N u)) *
      sH CB (sKB κ (sRho N κ w₂ (δ N u))) (δ N u) ^ 2 ≤
        6 * (81 * CB + 72) ^ 2 * N ^ (6 * e - w₂ + 3 * u) := by
  set ρ := sRho N κ w₂ (δ N u) with hρdef
  set KB := sKB κ ρ with hKBdef
  set H := sH CB KB (δ N u) with hHdef
  have hN0 : 0 < N := by linarith
  have hρ0 : 0 < ρ := sRho_pos hN hκ
  have hKB2 : 2 ≤ KB := two_le_sKB (by linarith) hρ0.le
  have hKB9 : KB ≤ 9 * κ := sKB_le hκ hρ1
  have hH := sH_le hN hu hκ hKB2 hKB9 (CB := CB)
  have hρle := sRho_le (w₂ := w₂) hN hu hκ
  have hH0 : 0 ≤ H := by
    rw [hHdef]; unfold sH
    have := delta_pos N u
    positivity
  have hpowκ : κ ^ 6 ≤ N ^ (6 * e) := by
    have h6 : N ^ (6 * e) = (N ^ e) ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    rw [h6]; exact pow_le_pow_left₀ (by linarith) hκe 6
  have hsplit : N ^ (6 * e - w₂ + 3 * u) = N ^ (6 * e) * (N ^ (-w₂ + u) * N ^ u * N ^ u) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  have hNw : 0 ≤ N ^ (-w₂ + u) := (Real.rpow_pos_of_pos hN0 _).le
  have hNu : 0 ≤ N ^ u := (Real.rpow_pos_of_pos hN0 _).le
  calc ρ / KB * H ^ 2 ≤ ρ / 2 * H ^ 2 := by
        gcongr
    _ ≤ (12 * κ ^ 2 * N ^ (-w₂ + u)) / 2 * ((81 * CB + 72) * κ ^ 2 * N ^ u) ^ 2 := by
        gcongr
    _ = 6 * (81 * CB + 72) ^ 2 * κ ^ 6 * (N ^ (-w₂ + u) * N ^ u * N ^ u) := by ring
    _ ≤ 6 * (81 * CB + 72) ^ 2 * N ^ (6 * e) * (N ^ (-w₂ + u) * N ^ u * N ^ u) := by
        gcongr
    _ = 6 * (81 * CB + 72) ^ 2 * N ^ (6 * e - w₂ + 3 * u) := by rw [hsplit]; ring

/-- The common width in power form. -/
theorem sgC_le_pow (hN : 1 ≤ N) (hu : 0 ≤ u) (he : 0 ≤ e) (hκ : 1 ≤ κ) (hκe : κ ≤ N ^ e)
    (CB : ℕ) (hρ1 : sRho N κ w₂ (δ N u) ≤ 1) :
    sgC (sRho N κ w₂ (δ N u)) (sRho N κ w₂ (δ N u) / sKB κ (sRho N κ w₂ (δ N u)) *
      sH CB (sKB κ (sRho N κ w₂ (δ N u))) (δ N u) ^ 2) κ ≤
        (24 + 24 * (81 * CB + 72) ^ 2) * N ^ (7 * e - w₂ + 3 * u) := by
  have hN0 : 0 < N := by linarith
  have hG := binWidth_le hN hu he hκ hκe CB hρ1 (w₂ := w₂)
  have hρle := sRho_le (w₂ := w₂) hN hu hκ
  set G := sRho N κ w₂ (δ N u) / sKB κ (sRho N κ w₂ (δ N u)) *
      sH CB (sKB κ (sRho N κ w₂ (δ N u))) (δ N u) ^ 2 with hGdef
  have hG0 : 0 ≤ G := by
    rw [hGdef]
    have := sRho_pos (w₂ := w₂) (u := u) hN hκ
    have := two_le_sKB (by linarith : (0 : ℝ) ≤ κ) this.le
    positivity
  unfold sgC
  have hκ2 : κ ^ 2 ≤ N ^ (2 * e) := by
    have h2 : N ^ (2 * e) = (N ^ e) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    rw [h2]; exact pow_le_pow_left₀ (by linarith) hκe 2
  have hmono1 : N ^ (2 * e - w₂ + u) ≤ N ^ (7 * e - w₂ + 3 * u) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hρpow : sRho N κ w₂ (δ N u) ≤ 12 * N ^ (2 * e - w₂ + u) := by
    have h1 : N ^ (2 * e - w₂ + u) = N ^ (2 * e) * N ^ (-w₂ + u) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [h1]
    calc sRho N κ w₂ (δ N u) ≤ 12 * κ ^ 2 * N ^ (-w₂ + u) := hρle
      _ ≤ 12 * N ^ (2 * e) * N ^ (-w₂ + u) := by
          have := Real.rpow_pos_of_pos hN0 (-w₂ + u)
          gcongr
      _ = _ := by ring
  have hGκ : G * κ ≤ 6 * (81 * CB + 72) ^ 2 * N ^ (7 * e - w₂ + 3 * u) := by
    have h1 : N ^ (7 * e - w₂ + 3 * u) = N ^ (6 * e - w₂ + 3 * u) * N ^ e := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [h1]
    calc G * κ ≤ 6 * (81 * CB + 72) ^ 2 * N ^ (6 * e - w₂ + 3 * u) * N ^ e :=
          mul_le_mul hG hκe (by linarith) (by positivity)
      _ = _ := by ring
  have hG1 : G ≤ G * κ := le_mul_of_one_le_right hG0 hκ
  have hNpos : 0 ≤ N ^ (7 * e - w₂ + 3 * u) := (Real.rpow_pos_of_pos hN0 _).le
  nlinarith

/-- The count ratio of paired full-time binning in power form. -/
theorem count_ratio_le (hN : 1 ≤ N) (hu : 0 ≤ u) (hκ : 1 ≤ κ) (hκe : κ ≤ N ^ e)
    (CB : ℕ) (hρ1 : sRho N κ w₂ (δ N u) ≤ 1) :
    sKB κ (sRho N κ w₂ (δ N u)) / (sRho N κ w₂ (δ N u) / sKB κ (sRho N κ w₂ (δ N u)) *
      sH CB (sKB κ (sRho N κ w₂ (δ N u))) (δ N u) ^ 2) ≤ 14 * N ^ (2 * e + w₂) := by
  set ρ := sRho N κ w₂ (δ N u) with hρdef
  set KB := sKB κ ρ with hKBdef
  set H := sH CB KB (δ N u) with hHdef
  have hN0 : 0 < N := by linarith
  have hρ0 : 0 < ρ := sRho_pos hN hκ
  have hρge : 6 * N ^ (-w₂) ≤ ρ := sRho_ge hN hu hκ
  have hKB2 : 2 ≤ KB := two_le_sKB (by linarith) hρ0.le
  have hKB9 : KB ≤ 9 * κ := sKB_le hκ hρ1
  have hH1 : 1 ≤ H := by
    rw [hHdef]; unfold sH
    have hδpos := delta_pos N u
    have hδle : δ N u ≤ 2 := by
      apply (delta_le_two_rpow_neg hN).trans
      have hh := Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hu)
      linarith only [hh]
    have hterm : 1 ≤ 8 * KB / δ N u :=
      (le_div_iff₀ hδpos).mpr (by linarith only [hKB2, hδle])
    have hCB0 : (0 : ℝ) ≤ CB := Nat.cast_nonneg _
    have hterm0 : 0 ≤ (CB : ℝ) * KB ^ 2 := by positivity
    linarith only [hterm, hterm0]
  have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH1
  have heq : KB / (ρ / KB * H ^ 2) = KB ^ 2 / (ρ * H ^ 2) := by
    field_simp
  rw [heq, div_le_iff₀ (by positivity)]
  have hκ2 : κ ^ 2 ≤ N ^ (2 * e) := by
    have h2 : N ^ (2 * e) = (N ^ e) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    rw [h2]; exact pow_le_pow_left₀ (by linarith) hκe 2
  have hsplit : N ^ (2 * e + w₂) * N ^ (-w₂) = N ^ (2 * e) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hpos : 0 ≤ N ^ (2 * e + w₂) := (Real.rpow_pos_of_pos hN0 _).le
  calc KB ^ 2 ≤ 81 * κ ^ 2 := by nlinarith
    _ ≤ 81 * N ^ (2 * e) := by linarith
    _ = 81 * (N ^ (2 * e + w₂) * N ^ (-w₂)) := by rw [hsplit]
    _ ≤ 14 * N ^ (2 * e + w₂) * (6 * N ^ (-w₂)) := by
        have := Real.rpow_pos_of_pos hN0 (-w₂)
        nlinarith
    _ ≤ 14 * N ^ (2 * e + w₂) * (ρ * 1) := by
        rw [mul_one]; gcongr
    _ ≤ 14 * N ^ (2 * e + w₂) * (ρ * H ^ 2) := by gcongr

end

end Submission.Obl.k4_raw_localized_native_systems.C
