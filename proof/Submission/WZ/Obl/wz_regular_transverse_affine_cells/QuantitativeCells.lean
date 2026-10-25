-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.QuantitativeCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.IteratePackets
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.RootPacket
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AssembleCells

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set Metric
open scoped ENNReal

lemma cells_of_iteration_parameters {n K N : ℕ} {δ ρ h S τ κ t θ : ℝ}
    {x v : Fin n → E} {Y : Fin n → Set E}
    (p : IterationParameters δ h S τ κ t θ N K)
    (hA : Admissible ρ δ n x v Y) (hnmax : (n : ℝ) ≤ δ ^ (-100 : ℝ))
    (hbottom : (1 / 2 : ℝ) ^ K * (384 * (n : ℝ)) ≤ 1)
    (hinit : 768 * τ ≤ ρ) (hret : h ≤ τ ^ (N * (2 * N + 5) + 2)) :
    Cells δ h n x v Y := by
  have hτ := p.tau_pos
  obtain ⟨C₀, hC₀, hregion, hrootcount⟩ :=
    initial_physical_packet hA p.delta_pos p.delta_small hτ hinit
  obtain ⟨L, hL, hLdisj, hLcount⟩ := iterate_physical_packets p hA.2.1 hA.2.2.1 hbottom C₀ hC₀
    (by rw [hregion]; exact volume_unit_closedBall_upper)
  obtain ⟨k, l, m, G, hG, hshape, hdisj, hcount⟩ :=
    select_common_cell_shape L (fun G hG => (hL G hG).1) hLdisj p.tau_shape
  have hmass : h * (n : ℝ) ≤ ∑ j, ((G j).indices.card : ℝ) := by
    calc h * (n : ℝ) ≤ τ ^ (N * (2 * N + 5) + 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hret (Nat.cast_nonneg _)
      _ = τ * (τ ^ (N * (2 * N + 5)) * (τ * (n : ℝ))) := by rw [pow_add]; ring
      _ ≤ τ * (τ ^ (N * (2 * N + 5)) * (C₀.indices.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrootcount (by positivity)) hτ.le
      _ ≤ τ * (L.map fun C => (C.indices.card : ℝ)).sum := mul_le_mul_of_nonneg_left hLcount hτ.le
      _ ≤ _ := hcount
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    subst m
    have hzero : h * (n : ℝ) ≤ 0 := by simpa using hmass
    have hn : (0 : ℝ) < n := by exact_mod_cast hA.1
    exact (not_le_of_gt (mul_pos p.quality_pos hn)) hzero
  exact cells_of_uniform_affine_cells hA.1 hnmax hm G k l hG hshape hdisj hmass

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
