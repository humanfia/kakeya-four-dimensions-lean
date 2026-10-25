-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg.GridPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.GridSmoothing

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg

open Set MeasureTheory
open scoped ENNReal

noncomputable def geometricWidth (t : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  t ^ ((k : ℝ) / (2 * N))

noncomputable def geometricError (t : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  3 * t ^ ((k : ℝ) / N)

noncomputable def geometricPadding (t ζ : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  t ^ ζ * geometricWidth t N k.succ

theorem geometricWidth_pos {t : ℝ} (ht : 0 < t) (N : ℕ) (k : Fin (N + 1)) :
    0 < geometricWidth t N k := Real.rpow_pos_of_pos ht _

theorem geometricWidth_le_one {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (N : ℕ) (k : Fin (N + 1)) : geometricWidth t N k ≤ 1 := by
  apply Real.rpow_le_one ht.le ht1
  positivity

theorem geometricPadding_pos {t ζ : ℝ} (ht : 0 < t) (N : ℕ) (k : Fin N) :
    0 < geometricPadding t ζ N k :=
  mul_pos (Real.rpow_pos_of_pos ht _) (geometricWidth_pos ht _ _)

theorem geometricPadding_le_one {t ζ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hζ : 0 ≤ ζ)
    (N : ℕ) (k : Fin N) : geometricPadding t ζ N k ≤ 1 := by
  exact (mul_le_mul (Real.rpow_le_one ht.le ht1 hζ)
    (geometricWidth_le_one ht ht1 _ _) (geometricWidth_pos ht _ _).le zero_le_one).trans_eq
      (one_mul _)

theorem geometricPadding_ratio {t ζ : ℝ} (ht : 0 < t) (N : ℕ) (k : Fin N) :
    geometricPadding t ζ N k / geometricWidth t N k.succ = t ^ ζ := by
  exact mul_div_cancel_right₀ _ (geometricWidth_pos ht _ _).ne'

theorem geometricWidth_ratio {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 0 < N) (k : Fin N) :
    geometricWidth t N k.succ / geometricWidth t N k.castSucc = t ^ (1 / (2 * (N : ℝ))) := by
  unfold geometricWidth
  rw [← Real.rpow_sub ht]
  congr 1
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem geometricError_step {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {N : ℕ} (hN : 0 < N) (k : Fin N) :
    geometricError t N k.succ + geometricError t N k.castSucc ≤ 6 * t ^ ((k : ℝ) / N) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hp : t ^ (((k : ℝ) + 1) / N) ≤ t ^ ((k : ℝ) / N) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1
      (div_le_div_of_nonneg_right (by linarith) hN0)
  simp only [geometricError, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  linarith

theorem geometric_second_budget {t ζ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    {N : ℕ} (hN : 0 < N) (k : Fin N) :
    (geometricError t N k.succ + geometricError t N k.castSucc) /
        (geometricPadding t ζ N k) ^ 2 ≤ 6 * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
  have hp := geometricPadding_pos (ζ := ζ) ht N k
  have hpow : (geometricPadding t ζ N k) ^ 2 =
      t ^ ((ζ + ((k : ℝ) + 1) / (2 * N)) * 2) := by
    unfold geometricPadding geometricWidth
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    rw [← Real.rpow_add ht, Real.rpow_mul ht.le, Real.rpow_two]
  calc
    _ ≤ (6 * t ^ ((k : ℝ) / N)) / (geometricPadding t ζ N k) ^ 2 :=
      div_le_div_of_nonneg_right (geometricError_step ht ht1 hN k) (sq_nonneg _)
    _ = 6 * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
      rw [hpow, mul_div_assoc, ← Real.rpow_sub ht]
      congr 2
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp
      ring

theorem geometric_first_budget {t ζ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hζ : 0 ≤ ζ)
    {N : ℕ} (hN : 0 < N) (k : Fin N) :
    (geometricError t N k.succ + geometricError t N k.castSucc) /
        geometricPadding t ζ N k ≤ 6 * t ^ (-(1 / (N : ℝ) + 2 * ζ)) := by
  have hp := geometricPadding_pos (ζ := ζ) ht N k
  have hp1 := geometricPadding_le_one ht ht1 hζ N k
  have hE : 0 ≤ geometricError t N k.succ + geometricError t N k.castSucc := by
    unfold geometricError
    positivity
  exact (div_le_div_of_nonneg_left hE (sq_pos_of_pos hp) (by nlinarith)).trans
    (geometric_second_budget ht ht1 hN k)

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Reg
