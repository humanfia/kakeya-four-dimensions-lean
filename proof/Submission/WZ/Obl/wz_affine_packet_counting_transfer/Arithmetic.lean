-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_packet_counting_transfer.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_affine_packet_counting_transfer

/-- Balance converts the fiber denominator into the required global density ratio. -/
theorem convex_arithmetic {C δ ρ h t m n k N q : ℝ}
    (hC : 384 ≤ C) (hδ : 0 < δ) (hρ : 0 < ρ) (hh : 0 < h) (ht : 0 < t)
    (hm : 0 ≤ m) (hn : 0 < n) (hk : 0 < k) (hN : 0 < N) (hq : 0 < q)
    (hb : h * n ≤ k * N * q) :
    384 * (m * (t / h) * ρ ^ 2 / (q * δ ^ 2)) ≤
      (C / h ^ 2) * m * (k * t * N * ρ ^ 2) / (n * δ ^ 2) := by
  let d := 384 * m * t * ρ ^ 2 / (h ^ 2 * q * n * δ ^ 2)
  calc
    _ = (h * n) * d := by dsimp [d]; field_simp
    _ ≤ (k * N * q) * d := mul_le_mul_of_nonneg_right hb (by dsimp [d]; positivity)
    _ = (384 / h ^ 2) * m * (k * t * N * ρ ^ 2) / (n * δ ^ 2) := by
      dsimp [d]
      field_simp
    _ ≤ _ := by gcongr

/-- The square-root loss from the slab theorem is absorbed by two powers of h. -/
theorem slab_arithmetic {C Cs h t l n k N q : ℝ}
    (hC : 4 * Cs ≤ C) (_hCs : 0 ≤ Cs) (hh : 0 < h) (hh1 : h ≤ 1)
    (ht : 0 < t) (hl : 0 ≤ l) (hn : 0 < n) (hk : 0 < k)
    (hb : h * n ≤ k * N * q)
    (hs : N * q ≤ (l * n) * (Cs * (16 * (t / h)) ^ (1/2 : ℝ))) :
    h ^ 2 ≤ C * l * k * t ^ (1/2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow] at hs ⊢
  have hroot : Real.sqrt (16 * (t / h)) = 4 * Real.sqrt t / Real.sqrt h := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_div ht.le]
    norm_num
    ring
  have hbound : h ≤ k * l * Cs * Real.sqrt (16 * (t / h)) := by
    apply (mul_le_mul_iff_of_pos_right hn).mp
    calc
      h * n ≤ k * N * q := hb
      _ ≤ k * ((l * n) * (Cs * Real.sqrt (16 * (t / h)))) := by nlinarith [mul_le_mul_of_nonneg_left hs hk.le]
      _ = _ := by ring
  rw [hroot] at hbound
  have hbound' : h * Real.sqrt h ≤ 4 * Cs * l * k * Real.sqrt t := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hh)).mp
    convert hbound using 1; ring
  calc
    h ^ 2 ≤ h * Real.sqrt h := by
      nlinarith [mul_le_mul_of_nonneg_left (Real.le_sqrt_self_iff.mpr hh1) hh.le]
    _ ≤ 4 * Cs * l * k * Real.sqrt t := hbound'
    _ ≤ _ := by gcongr

/-- Packing one fiber and taking square roots yields the third quantitative bound. -/
theorem packing_arithmetic {C Cp δ ρ h t n k N q : ℝ}
    (hC : 384 * Cp ≤ C) (hCp : 1 ≤ Cp)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hh : 0 < h) (hh1 : h ≤ 1) (ht : 0 < t)
    (_hn : 0 < n) (hk : 0 < k) (hN : 0 < N) (hq : 0 < q)
    (hb : h * n ≤ k * N * q)
    (hp : q * δ ^ 4 ≤ Cp * ((t / h) * (384 * ρ ^ 2)) ^ 2) :
    δ ^ 2 * (n / (k * N)) ^ (1/2 : ℝ) ≤ (C / h ^ 2) * t * ρ ^ 2 := by
  have hCp0 : 0 ≤ Cp := by linarith
  have hp' : δ ^ 2 * Real.sqrt q ≤ Cp * ((t / h) * (384 * ρ ^ 2)) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    calc
      (δ ^ 2 * Real.sqrt q) ^ 2 = q * δ ^ 4 := by rw [mul_pow, Real.sq_sqrt hq.le]; ring
      _ ≤ Cp * ((t / h) * (384 * ρ ^ 2)) ^ 2 := hp
      _ ≤ Cp ^ 2 * ((t / h) * (384 * ρ ^ 2)) ^ 2 := by
        gcongr
        nlinarith
      _ = _ := by ring
  have hb' : n / (k * N) ≤ q / h := by
    apply (div_le_div_iff₀ (mul_pos hk hN) hh).mpr
    nlinarith only [hb]
  have hroot : h ^ 2 ≤ h * Real.sqrt h := by
    nlinarith [mul_le_mul_of_nonneg_left (Real.le_sqrt_self_iff.mpr hh1) hh.le]
  rw [← Real.sqrt_eq_rpow]
  calc
    δ ^ 2 * Real.sqrt (n / (k * N)) ≤ δ ^ 2 * Real.sqrt (q / h) := by
      gcongr
    _ = (δ ^ 2 * Real.sqrt q) / Real.sqrt h := by rw [Real.sqrt_div hq.le]; ring
    _ ≤ (Cp * ((t / h) * (384 * ρ ^ 2))) / Real.sqrt h := by gcongr
    _ = (384 * Cp * t * ρ ^ 2) / (h * Real.sqrt h) := by ring
    _ ≤ (384 * Cp * t * ρ ^ 2) / h ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hh) hroot
    _ = ((384 * Cp) / h ^ 2) * t * ρ ^ 2 := by ring
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_affine_packet_counting_transfer
