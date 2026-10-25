-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.PacketPower.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DyadicPower

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces

/-- Compose two power losses and absorb a constant into a third one. -/
theorem triple_loss_absorption {δ ε : ℝ} (hδ : 0 < δ) {K A B : ENNReal}
    (hK : K * o (δ ^ ε) ≤ 1)
    (h : o (δ ^ ε) * A ≤ (K * o (δ ^ (-ε))) * B) :
    o (δ ^ (3 * ε)) * A ≤ B := by
  have hmul (s t : ℝ) : o (δ ^ s) * o (δ ^ t) = o (δ ^ (s + t)) := by
    dsimp only [o]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), ← Real.rpow_add hδ]
  calc
    _ = o (δ ^ (2 * ε)) * (o (δ ^ ε) * A) := by
      rw [← mul_assoc, hmul, show 2 * ε + ε = 3 * ε by ring]
    _ ≤ o (δ ^ (2 * ε)) * ((K * o (δ ^ (-ε))) * B) := mul_le_mul_right h _
    _ = (K * (o (δ ^ (2 * ε)) * o (δ ^ (-ε)))) * B := by ac_rfl
    _ = (K * o (δ ^ ε)) * B := by
      rw [hmul, show 2 * ε + -ε = ε by ring]
    _ ≤ 1 * B := mul_le_mul_left hK _
    _ = _ := one_mul _

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces
