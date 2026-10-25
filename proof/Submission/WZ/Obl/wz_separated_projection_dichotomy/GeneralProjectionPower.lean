-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.GeneralProjectionPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionNumerics

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem projection_power_with_constant {A δ τ ε t : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hτ : 0 < τ) (hε : 0 < ε)
    (hτbound : τ ≤ δ ^ t) (hbudget : A * δ ^ (t * ε / 2) ≤ 1) :
    (A / τ) ^ (1 - ε) ≤ τ ^ (ε / 2 - 1) := by
  have hApow : A ^ (1 - ε) ≤ A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA
      (show 1 - ε ≤ 1 by linarith)
  have hτpow : τ ^ (ε / 2) ≤ δ ^ (t * ε / 2) := by
    calc τ ^ (ε / 2) ≤ (δ ^ t) ^ (ε / 2) :=
        Real.rpow_le_rpow hτ.le hτbound (by positivity)
      _ = _ := by rw [← Real.rpow_mul hδ.le]; congr 1; ring
  have hprod : A ^ (1 - ε) * τ ^ (ε / 2) ≤ 1 :=
    (mul_le_mul hApow hτpow (by positivity) (zero_le_one.trans hA)).trans hbudget
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hτ (1 - ε / 2))).mp
  rw [← Real.rpow_add hτ, show ε / 2 - 1 + (1 - ε / 2) = 0 by ring, Real.rpow_zero]
  calc (A / τ) ^ (1 - ε) * τ ^ (1 - ε / 2) =
        A ^ (1 - ε) * τ ^ (ε / 2) := by
          rw [Real.div_rpow (zero_le_one.trans hA) hτ.le]
          have heq : A ^ (1 - ε) / τ ^ (1 - ε) * τ ^ (1 - ε / 2) =
              A ^ (1 - ε) * (τ ^ (1 - ε / 2) / τ ^ (1 - ε)) := by ring
          rw [heq, ← Real.rpow_sub hτ]
          congr 2
          ring
    _ ≤ 1 := hprod

end WangZahlLot.Obl.wz_separated_projection_dichotomy
