-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPackingPowerBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPackingPowerBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPackingPowerBudgets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPackingPowerBudgets.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPackingPowerBudgets.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSecondScaleBudgets

/-! Convert the fixed entropy/angular exponent gaps into the actual packing
and pair-overlap hypotheses. Only the original coarse-heavy floor occurs. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

theorem strip_power_product_pow {N : ℝ} (hN : 0 ≤ N) (E : ℝ) (p n : ℕ) (a : ℝ) :
    (E ^ p * N ^ a) ^ n = E ^ (n * p) * N ^ ((n : ℝ) * a) := by
  have hE : (E ^ p) ^ n = E ^ (n * p) := by rw [← pow_mul, Nat.mul_comm]
  have hR : (N ^ a) ^ n = N ^ ((n : ℝ) * a) := by
    simpa only [mul_comm] using (Real.rpow_mul_natCast hN a n).symm
  rw [mul_pow, hE, hR]

theorem strip_heavy_net_count_envelope {N E floor count a : ℝ}
    (hN : 1 ≤ N) (hE : 1 ≤ E) (hfloor : 0 < floor) (p : ℕ) (ha : 0 ≤ a)
    (hInv : floor⁻¹ ≤ E ^ p * N ^ a) (hcount : count ≤ 2 / floor ^ 2 + 1) :
    count ≤ 3 * (E ^ p * N ^ a) ^ 2 := by
  have hH : 1 ≤ E ^ p * N ^ a := by
    simpa only [one_mul] using mul_le_mul (one_le_pow₀ hE (n := p))
      (Real.one_le_rpow hN ha) (by norm_num) (by positivity)
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ floor⁻¹) hInv 2
  have hid : 2 / floor ^ 2 + 1 = 2 * (floor⁻¹) ^ 2 + 1 := by field_simp
  rw [hid] at hcount
  nlinarith [one_le_pow₀ hH (n := 2)]

theorem strip_packing_error_of_power_budget {N E floor ε a v : ℝ}
    (hN : 0 < N) (hE : 1 ≤ E) (hfloor : 0 < floor) (hε : 0 ≤ ε)
    (p q : ℕ) (hInv : floor⁻¹ ≤ E ^ p * N ^ a) (hcap : ε ≤ E ^ q * N ^ (-v))
    (hbudget : 2 * E ^ (q + 2 * p) * N ^ (2 * a - v) ≤ 1) :
    2 * ε ≤ floor ^ 2 := by
  have hsq : (floor⁻¹) ^ 2 ≤ E ^ (2 * p) * N ^ (2 * a) := by
    calc
      _ ≤ (E ^ p * N ^ a) ^ 2 := pow_le_pow_left₀ (by positivity) hInv 2
      _ = _ := by simpa only [Nat.cast_ofNat] using strip_power_product_pow hN.le E p 2 a
  have hproduct : 2 * ε * (floor⁻¹) ^ 2 ≤ 1 := by
    calc
      _ ≤ 2 * (E ^ q * N ^ (-v)) * (E ^ (2 * p) * N ^ (2 * a)) := by gcongr
      _ = 2 * E ^ (q + 2 * p) * N ^ (2 * a - v) := by
        rw [pow_add, show 2 * a - v = 2 * a + (-v) by ring, Real.rpow_add hN]
        ring
      _ ≤ _ := hbudget
  have hquot : 2 * ε / floor ^ 2 ≤ 1 := by
    simpa only [div_eq_mul_inv, inv_pow] using hproduct
  exact (div_le_one (sq_pos_of_pos hfloor)).mp hquot

theorem strip_pair_overlap_of_power_budget {N E count ε a v : ℝ}
    (hN : 0 < N) (hE : 1 ≤ E) (hcount0 : 0 ≤ count) (hε : 0 ≤ ε)
    (p q : ℕ) (hcount : count ≤ 3 * (E ^ p * N ^ a) ^ 2)
    (hcap : ε ≤ E ^ q * N ^ (-v))
    (hbudget : 900 * E ^ (4 * p + q + 8) * N ^ (4 * a - v) ≤ 1) :
    count ^ 2 * ε ≤ (100 * E ^ 8)⁻¹ := by
  have hsq : count ^ 2 ≤ 9 * (E ^ p * N ^ a) ^ 4 := by
    calc
      _ ≤ (3 * (E ^ p * N ^ a) ^ 2) ^ 2 := pow_le_pow_left₀ hcount0 hcount 2
      _ = _ := by ring
  have hraw : count ^ 2 * ε ≤ 9 * E ^ (4 * p + q) * N ^ (4 * a - v) := by
    calc
      _ ≤ (9 * (E ^ p * N ^ a) ^ 4) * (E ^ q * N ^ (-v)) :=
        mul_le_mul hsq hcap hε (by positivity)
      _ = _ := by
        rw [strip_power_product_pow hN.le E p 4 a, pow_add,
          show 4 * a - v = 4 * a + (-v) by ring, Real.rpow_add hN]
        norm_num only [Nat.cast_ofNat]
        ring
  have hproduct : (count ^ 2 * ε) * (100 * E ^ 8) ≤ 1 := by
    calc
      _ ≤ (9 * E ^ (4 * p + q) * N ^ (4 * a - v)) * (100 * E ^ 8) := by gcongr
      _ = 900 * E ^ (4 * p + q + 8) * N ^ (4 * a - v) := by rw [pow_add]; ring
      _ ≤ _ := hbudget
  rw [← one_div]
  exact (le_div_iff₀ (by positivity : 0 < 100 * E ^ 8)).mpr hproduct

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
