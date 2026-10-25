-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_finite_load_selection.Entropy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_nsp_finite_load_selection

lemma log_test_count_bound {d ε r : ℝ} {H : ℕ}
    (hd : 1 ≤ d) (hε : 0 < ε) (hr : 0 < r) (hr1 : r ≤ 1)
    (hH : (H : ℝ) ≤ d * r ^ (-d)) :
    Real.log ((H : ℝ) + 1) ≤ Real.log (d + 1) + (d / ε) * r ^ (-ε) := by
  have hd0 : 0 ≤ d := by linarith
  have hrpow : 1 ≤ r ^ (-d) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have hH' : (H : ℝ) + 1 ≤ (d + 1) * r ^ (-d) := by nlinarith
  have hlog := Real.neg_rpow_div_le_log hr.le hε
  have hlog' : -d * Real.log r ≤ (d / ε) * r ^ (-ε) := by
    have := mul_le_mul_of_nonneg_left hlog hd0
    nlinarith [show d * (-r ^ (-ε) / ε) = -(d / ε) * r ^ (-ε) by ring]
  calc
    Real.log ((H : ℝ) + 1) ≤ Real.log ((d + 1) * r ^ (-d)) :=
      Real.log_le_log (by positivity) hH'
    _ = Real.log (d + 1) + -d * Real.log r := by
      rw [Real.log_mul (by positivity) (ne_of_gt (Real.rpow_pos_of_pos hr _)),
        Real.log_rpow hr]
    _ ≤ Real.log (d + 1) + (d / ε) * r ^ (-ε) := add_le_add le_rfl hlog'

lemma entropy_absorption (a d : ℝ) (ha : 1 ≤ a) (hd : 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (K H : ℕ),
      0 < r → r ≤ 1 → (H : ℝ) ≤ d * r ^ (-d) →
      (Real.exp 1 - 1) * a + Real.log ((K : ℝ) + 1) + Real.log ((H : ℝ) + 1) ≤
        C * r ^ (-ε) * Real.log (2 + (K : ℝ)) := by
  let A := (Real.exp 1 - 1) * a + Real.log (d + 1)
  let B := A + d / ε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ a := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hb0 : 0 ≤ Real.exp 1 - 1 := by
    have := Real.add_one_le_exp 1
    linarith
  have hA : 0 ≤ A := add_nonneg (mul_nonneg hb0 ha0)
    (Real.log_nonneg (by linarith))
  have hB : 0 ≤ B := add_nonneg hA (div_nonneg hd0 hε.le)
  refine ⟨1 + B / Real.log 2, by positivity, ?_⟩
  intro r K H hr hr1 hH
  have hR : 1 ≤ r ^ (-ε) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have hR0 : 0 ≤ r ^ (-ε) := (Real.rpow_pos_of_pos hr _).le
  have hL : Real.log 2 ≤ Real.log (2 + (K : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) K])
  have hL0 : 0 ≤ Real.log (2 + (K : ℝ)) := hlog2.le.trans hL
  have hK : Real.log ((K : ℝ) + 1) ≤ Real.log (2 + (K : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have hHlog := log_test_count_bound hd hε hr hr1 hH
  have hBR : B ≤ B / Real.log 2 * Real.log (2 + (K : ℝ)) := by
    calc
      B = B / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ B / Real.log 2 * Real.log (2 + (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hL (div_nonneg hB hlog2.le)
  calc
    (Real.exp 1 - 1) * a + Real.log ((K : ℝ) + 1) + Real.log ((H : ℝ) + 1) ≤
        A + Real.log (2 + (K : ℝ)) + (d / ε) * r ^ (-ε) := by
      dsimp [A]
      linarith
    _ ≤ B * r ^ (-ε) + r ^ (-ε) * Real.log (2 + (K : ℝ)) := by
      have hAR := mul_le_mul_of_nonneg_left hR hA
      have hLR := mul_le_mul_of_nonneg_right hR hL0
      dsimp [B]
      nlinarith
    _ ≤ (B / Real.log 2 * Real.log (2 + (K : ℝ))) * r ^ (-ε) +
        r ^ (-ε) * Real.log (2 + (K : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hBR hR0) le_rfl
    _ = (1 + B / Real.log 2) * r ^ (-ε) * Real.log (2 + (K : ℝ)) := by ring

end WangZahlLot.Obl.wz_nsp_finite_load_selection
