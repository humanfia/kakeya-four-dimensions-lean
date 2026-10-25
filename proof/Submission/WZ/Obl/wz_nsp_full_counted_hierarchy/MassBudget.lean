-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.MassBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Arithmetic

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open scoped BigOperators

/-- The per-edge upper ceiling estimate pays for all motions, including the
loss in selecting the initial dense subfamily. -/
theorem motion_mass_budget {δ u a H : ℝ} {B J : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hu : 0 < u)
    (hua : u * ((B : ℝ) + 1) ≤ a) (hJB : J ≤ B)
    (D n : ℕ → ℕ) (r : ℕ → ℝ) (hrJ : r J = δ)
    (hroot : (n 0 : ℝ) * (r 0) ^ 2 ≤ 1)
    (hH : δ ^ u * H ≤ (n J : ℝ))
    (hstep : ∀ j, j < J → (D j : ℝ) * ((n (j + 1) : ℝ) * (r (j + 1)) ^ 2) ≤
      (49 * δ ^ (-u)) * ((n j : ℝ) * (r j) ^ 2)) :
    ((∏ j ∈ Finset.range J, D j : ℕ) : ℝ) * H * δ ^ 2 ≤ 49 ^ B * δ ^ (-a) := by
  have hpow : 0 ≤ δ ^ (-u) := Real.rpow_nonneg hδ.le _
  have hH' : H ≤ δ ^ (-u) * (n J : ℝ) := by
    calc
      H = δ ^ (-u) * (δ ^ u * H) := by
        rw [← mul_assoc, ← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH hpow
  have hmass := copy_mass_telescopes D (fun j => (n j : ℝ) * (r j) ^ 2)
    (49 * δ ^ (-u)) (by positivity) J hstep
  have hmass' : ((∏ j ∈ Finset.range J, D j : ℕ) : ℝ) * ((n J : ℝ) * δ ^ 2) ≤
      (49 * δ ^ (-u)) ^ J := by
    simpa only [hrJ] using hmass.trans (mul_le_of_le_one_right (by positivity) hroot)
  have hexp : u * ((J : ℝ) + 1) ≤ a := by
    have hJB' : (J : ℝ) ≤ B := Nat.cast_le.mpr hJB
    nlinarith
  calc
    _ ≤ δ ^ (-u) * (((∏ j ∈ Finset.range J, D j : ℕ) : ℝ) * ((n J : ℝ) * δ ^ 2)) := by
      have hh := mul_le_mul_of_nonneg_left hH'
        (show 0 ≤ ((∏ j ∈ Finset.range J, D j : ℕ) : ℝ) * δ ^ 2 by positivity)
      nlinarith only [hh]
    _ ≤ δ ^ (-u) * (49 * δ ^ (-u)) ^ J := mul_le_mul_of_nonneg_left hmass' hpow
    _ = 49 ^ J * δ ^ (-u * ((J : ℝ) + 1)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hδ.le]
      rw [show -u * ((J : ℝ) + 1) = -u + -u * J by ring, Real.rpow_add hδ]
      ring
    _ ≤ 49 ^ B * δ ^ (-a) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) hJB
      · exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      · positivity
      · positivity

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
