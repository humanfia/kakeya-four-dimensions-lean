-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarPacking.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.LocalSumPacking
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RealCoverAlgebra

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open scoped Pointwise

/-- Frostman control supplies a covering lower bound at every allowed scale. -/
theorem RealFiniteFrostman.cover_lower {δ C β ρ : ℝ} {S : Finset ℝ}
    (hF : RealFiniteFrostman δ C β S) (hS : S.Nonempty)
    (hC : 0 < C) (hρ : 0 < ρ) (hδρ : δ ≤ ρ) :
    CoverLower ρ (↑S : Set ℝ) (C * ρ ^ β)⁻¹ := by
  intro m cc hc
  have hcard := WangZahlLot.Obl.wz_separated_projection_dichotomy.card_le_cover_mul_fiber_bound
    S id (by simpa only [Covers, WangZahlLot.Obl.wz_separated_projection_dichotomy.Covers, Set.image_id] using hc) (fun i => hF (cc i) ρ hδρ)
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hpos : 0 < C * ρ ^ β := mul_pos hC (Real.rpow_pos_of_pos hρ _)
  have hunit : 1 ≤ (m : ℝ) * (C * ρ ^ β) := by nlinarith
  apply (inv_le_iff_one_le_mul₀ hpos).mpr
  nlinarith

/-- If adding a nonconcentrated set does not increase entropy much, the
other summand inherits its nonconcentration. -/
theorem frostman_of_small_sum (R S : Finset ℝ) {δ C β K : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : 0 ≤ K) (hS : S.Nonempty) (hSF : RealFiniteFrostman δ C β S)
    (hRsep : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → δ ≤ dist a b)
    (hsmall : RealCoverBound (2 * δ) (R + S) (K * (R.card : ℝ))) :
    RealFiniteFrostman δ (144 * C * K) β R := by
  obtain ⟨m, cc, hc, hm⟩ := hsmall
  intro x ρ hδρ
  have hρ : 0 < ρ := hδ.trans_le hδρ
  have h8ρ : 0 < 8 * ρ := by positivity
  have hL := hSF.cover_lower hS hC h8ρ (by linarith)
  have hh := local_sum_packing_count (x := x) hδ hδρ R S hRsep hL cc
    (hc.mono_radius (by linarith : 2 * δ ≤ 3 * δ))
  have hp : 0 < C * (8 * ρ) ^ β := by positivity
  have hmul := mul_le_mul_of_nonneg_right hh hp.le
  rw [mul_assoc, inv_mul_cancel₀ hp.ne', mul_one] at hmul
  have hp8 : (8 : ℝ) ^ β ≤ 8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hβ1
  calc
    ((R.filter (fun a => dist a x ≤ ρ)).card : ℝ) ≤ 18 * (m : ℝ) * (C * (8 * ρ) ^ β) := hmul
    _ ≤ 18 * (K * (R.card : ℝ)) * (C * ((8 : ℝ) ^ β * ρ ^ β)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hρ.le]
      gcongr
    _ ≤ 18 * (K * (R.card : ℝ)) * (C * (8 * ρ ^ β)) := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
