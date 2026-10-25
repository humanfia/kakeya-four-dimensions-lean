import Submission.Obl.k4_scalar_initial_true_horizon.InitialCells
import Submission.Obl.k4_scalar_initial_true_horizon.InitialDyadic

/-!
# Dyadic plank caps of bad long trajectories and their collision energy

At the dyadic widths `w_i = 2^(i+1) ε`, `ε = q / 2^(kmax + s)`, the bad long trajectories
of a group obey the cap `A w_i min(1, w_i / w₁)`, `w₁ = q / 2^kmax`: below `w₁` by the
polynomial density of the prior, between `w₁` and `q` by the light cells of the exact
level, and above `q` by the light top-level cells.  Feeding these caps into the planar
collision estimate gives the collision hypothesis of the group bound.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial hidden)

/-- The dyadic cap at the widths of the collision estimate. -/
theorem badLong_dyadic_cap (ν : Measure Coeff) {E : Set (Coeff × ℝ)} (hE : MeasurableSet E)
    {Nb Kb aL q t₀ Φf φ₀ Rd : ℝ} (hq : 0 < q) (hφ₀ : 0 < φ₀) (hΦf : 0 ≤ Φf) (m : ℤ)
    (kmax r s : ℕ)
    (hdens : ∀ l₀ : Coeff, ∀ w : ℝ, 0 < w →
      ν {l | bddTraj Nb Kb l ∧ xBin aL t₀ l = m ∧
        l ∈ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w} ≤
        ENNReal.ofReal (Rd * w ^ 2 / q))
    (hRd : Rd * (q / 2 ^ kmax) ≤ 30 * 2 ^ r * Φf / φ₀) (l₀ : Coeff)
    {i : ℕ} (hi : i ≤ s + (kmax + r)) :
    (ν.restrict (badLong ((ν.prod volume).restrict E) E Nb Kb aL q t₀ Φf φ₀ m kmax))
        (plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀
          (2 ^ (i + 1) * ((q / 2 ^ kmax) / 2 ^ s))) ≤
      ENNReal.ofReal ((30 * 2 ^ r * Φf / (φ₀ * q)) *
        (2 ^ (i + 1) * ((q / 2 ^ kmax) / 2 ^ s)) *
          min 1 (2 ^ (i + 1) * ((q / 2 ^ kmax) / 2 ^ s) / (q / 2 ^ kmax))) := by
  set BL := badLong ((ν.prod volume).restrict E) E Nb Kb aL q t₀ Φf φ₀ m kmax with hBL
  set w₁ : ℝ := q / 2 ^ kmax with hw₁
  set w : ℝ := 2 ^ (i + 1) * (w₁ / 2 ^ s) with hw
  set A : ℝ := 30 * 2 ^ r * Φf / (φ₀ * q) with hA
  have hw₁pos : 0 < w₁ := by positivity
  have hwpos : 0 < w := by positivity
  have hBLm : MeasurableSet BL := measurableSet_badLong _ hE _ _ _ _ _ _ _ m kmax
  rw [Measure.restrict_apply' hBLm, inter_comm]
  have hratio : w / w₁ = 2 ^ (i + 1) / 2 ^ s := by rw [hw]; field_simp
  rcases lt_or_ge (i + 1) s with hsmall | hbig
  · -- below the finest cell width: polynomial density of the prior
    have hlt : w / w₁ < 1 := by
      rw [hratio, div_lt_one (by positivity)]
      exact pow_lt_pow_right₀ (by norm_num) hsmall
    rw [min_eq_right hlt.le]
    calc ν (BL ∩ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w)
        ≤ ν {l | bddTraj Nb Kb l ∧ xBin aL t₀ l = m ∧
            l ∈ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w} := by
          apply measure_mono
          rintro l ⟨hlB, hlp⟩
          exact ⟨hlB.1, hlB.2.1, hlp⟩
      _ ≤ ENNReal.ofReal (Rd * w ^ 2 / q) := hdens l₀ w hwpos
      _ ≤ ENNReal.ofReal (A * w * (w / w₁)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hA]
          have hRd' : Rd ≤ 30 * 2 ^ r * Φf / φ₀ / w₁ := by
            rw [le_div_iff₀ hw₁pos]; exact hRd
          calc Rd * w ^ 2 / q ≤ (30 * 2 ^ r * Φf / φ₀ / w₁) * w ^ 2 / q := by
                gcongr
            _ = 30 * 2 ^ r * Φf / (φ₀ * q) * w * (w / w₁) := by
                field_simp
  · have hge : 1 ≤ w / w₁ := by
      rw [hratio, one_le_div (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) hbig
    rw [min_eq_left hge, mul_one]
    rcases le_or_gt (i + 1) (s + kmax) with hmid | htop
    · -- exact level `kmax + s - (i + 1)`
      set k := kmax + s - (i + 1) with hk
      have hkle : k ≤ kmax := by omega
      have hwk : w = q / 2 ^ k := by
        rw [hw, hw₁]
        have hexp : kmax = k + (i + 1) - s := by omega
        have h2 : (2 : ℝ) ^ (i + 1) * 2 ^ k = 2 ^ kmax * 2 ^ s := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        field_simp
        linarith [h2]
      have hcap := badLong_plank_le ν hE (Nb := Nb) (Kb := Kb) (aL := aL) (t₀ := t₀)
        hq hφ₀ hΦf m hkle l₀ hwpos.le
      refine hcap.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hwk]
      have hJ : cellJ q k = w := by rw [cellJ, hwk]
      rw [hJ]
      have this : 2 * w / w = 2 := by field_simp
      have h4 : 4 * w / w = 4 := by field_simp
      rw [this, h4, hA]
      have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
      have hΦ : 0 ≤ Φf * w / (φ₀ * q) := by positivity
      calc (2 + 2) * (4 + 2) * (Φf * w / (φ₀ * q)) = 24 * (Φf * w / (φ₀ * q)) := by ring
        _ ≤ 30 * 2 ^ r * (Φf * w / (φ₀ * q)) := by nlinarith
        _ = 30 * 2 ^ r * Φf / (φ₀ * q) * w := by ring
    · -- above the block length: top-level cells
      have hcap := badLong_plank_le ν hE (Nb := Nb) (Kb := Kb) (aL := aL) (t₀ := t₀)
        hq hφ₀ hΦf m (Nat.zero_le kmax) l₀ hwpos.le
      refine hcap.trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [pow_zero, div_one, cellJ]
      -- `2 q ≤ w ≤ 2^(r+1) q`
      have hwq : w / q = 2 ^ (i + 1) / 2 ^ (s + kmax) := by
        rw [hw, hw₁]; field_simp; ring
      have hlow : 2 ≤ w / q := by
        rw [hwq, le_div_iff₀ (by positivity)]
        have : (2 : ℝ) ^ (i + 1) = 2 ^ (s + kmax) * 2 ^ (i + 1 - (s + kmax)) := by
          rw [← pow_add]; congr 1; omega
        rw [this]
        have : (2 : ℝ) ≤ 2 ^ (i + 1 - (s + kmax)) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (i + 1 - (s + kmax)) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (s + kmax)]
      have hup : w / q ≤ 2 * 2 ^ r := by
        rw [hwq, div_le_iff₀ (by positivity)]
        have : (2 : ℝ) ^ (i + 1) ≤ 2 ^ (s + kmax + (r + 1)) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        calc (2 : ℝ) ^ (i + 1) ≤ 2 ^ (s + kmax + (r + 1)) := this
          _ = 2 * 2 ^ r * 2 ^ (s + kmax) := by ring
      set x := w / q with hx
      have hwx : w = x * q := by rw [hx]; field_simp
      have h1 : 2 * w / q + 2 ≤ 3 * x := by rw [mul_div_assoc, ← hx]; linarith
      have h2 : 4 * w / q + 2 ≤ 5 * x := by rw [mul_div_assoc, ← hx]; linarith
      have hΦ : 0 ≤ Φf * q / (φ₀ * q) := by positivity
      calc (2 * w / q + 2) * (4 * w / q + 2) * (Φf * q / (φ₀ * q))
          ≤ (3 * x) * (5 * x) * (Φf * q / (φ₀ * q)) := by
            gcongr
      _ = 15 * x * (Φf * (x * q) / (φ₀ * q)) := by ring
      _ ≤ 15 * (2 * 2 ^ r) * (Φf * (x * q) / (φ₀ * q)) := by
            gcongr
      _ = A * w := by rw [hA, hwx]; ring

end Submission.Obl.k4_scalar_initial_true_horizon
