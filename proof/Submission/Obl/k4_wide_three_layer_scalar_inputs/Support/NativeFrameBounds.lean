import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Good
import Submission.Obl.k4_horizontal_supercritical_three_projections.RawIndex

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory

noncomputable section

open Submission.Obl.k4_critical_conditional_row_preparation

/-- The exact dyadic frame also satisfies the coarser power bounds used
by every raw mesh and field budget. -/
theorem native_frame_scale_bounds {α : Type} [MeasurableSpace α]
    {cfg : Data α} {k : ℕ} {s R : ℝ} (hB : BlocksAt cfg k s R)
    (hN : 1 ≤ cfg.N k) (hK : 1 ≤ cfg.K k) (hs : 0 ≤ s)
    (hκ : 0 < cfg.κ) (hκ1 : cfg.κ ≤ 1)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) :
    let F := blockFrame cfg k s i L
    0 < F.q ∧ F.q ≤ 1 ∧ cfg.N k ^ (-s) / cfg.K k ≤ F.q ∧
      0 < F.g ∧ F.g ≤ 1 ∧ cfg.N k ^ (-s) ≤ F.g ∧
      0 < F.a ∧ F.a ≤ 1 := by
  dsimp only [blockFrame]
  have hNp : 0 < cfg.N k := zero_lt_one.trans_le hN
  have hκs : cfg.κ * s ≤ s := mul_le_of_le_one_left hs hκ1
  have hlen := Submission.Obl.k4_horizontal_supercritical_three_projections.block_length_bounds
    hNp hK hB.T_lo hB.T_hi
  simp only [zpow_neg, zpow_natCast] at hlen
  refine ⟨by positivity,
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)),
    ?_, Real.rpow_pos_of_pos hNp _, ?_, ?_, Real.rpow_pos_of_pos hNp _, ?_⟩
  · exact (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
        (zero_le_one.trans hK)).trans hlen.1
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
