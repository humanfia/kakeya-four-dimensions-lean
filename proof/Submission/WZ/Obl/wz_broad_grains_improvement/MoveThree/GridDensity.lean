-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GridDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GridDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PowerGrid
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DensityCut

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (ballDensity_mass ballDensity_bounds)

/-- Upper bounds on a finite multiplicative mesh control every radius;
below the fine scale the ambient volume bound suffices. -/
theorem density_upper_of_power_grid {δ q t s : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hq : 0 < q) (hN : 0 < N) (hscale : q ^ N = δ)
    (hs : 0 ≤ s) (hbase : 8 ≤ δ ^ (-t))
    (hmesh : δ ^ (-(t / 2)) ≤ δ ^ (-t) * q ^ 3)
    (U : Set V) (p : V)
    (hgrid : ∀ j : Fin N, μ (U ∩ ball p (q ^ j.val)) ≤
      O (δ ^ (-(t / 2)) * (δ / q ^ j.val) ^ s * (q ^ j.val) ^ 3)) :
    ∀ r : ℝ, 0 < r → r ≤ 1 → μ (U ∩ ball p r) ≤
      O (δ ^ (-t) * (δ / r) ^ s * r ^ 3) := by
  intro r hr hr1
  by_cases hlow : δ ≤ r
  · obtain ⟨j, hjlow, hjupp⟩ := finite_power_grid_cover N hN (hscale ▸ hlow) hr1
    have hR : 0 < q ^ j.val := pow_pos hq _
    have hratio : δ / q ^ j.val ≤ δ / r :=
      div_le_div_of_nonneg_left hδ.le hr hjupp
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ δ / q ^ j.val) hratio hs
    have hrad : q * q ^ j.val ≤ r := by simpa only [pow_succ, mul_comm] using hjlow
    have hcube := pow_le_pow_left₀ (by positivity : 0 ≤ q * q ^ j.val) hrad 3
    calc
      _ ≤ μ (U ∩ ball p (q ^ j.val)) :=
        measure_mono (inter_subset_inter_right _ (ball_subset_ball hjupp))
      _ ≤ _ := hgrid j
      _ ≤ O (δ ^ (-t) * (δ / r) ^ s * r ^ 3) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (δ ^ (-t) * q ^ 3) * (δ / r) ^ s * (q ^ j.val) ^ 3 := by gcongr
          _ = δ ^ (-t) * (δ / r) ^ s * (q * q ^ j.val) ^ 3 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hcube (by positivity)
  · have hratio : 1 ≤ δ / r := (le_div_iff₀ hr).mpr (by simpa using (le_of_not_ge hlow))
    have hp : 1 ≤ (δ / r) ^ s := Real.one_le_rpow hratio hs
    have hdensity : 8 ≤ δ ^ (-t) * (δ / r) ^ s := by
      nlinarith [Real.rpow_nonneg hδ.le (-t)]
    change volume (U ∩ ball p r) ≤ _
    rw [← ballDensity_mass U p hr]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right ((ballDensity_bounds U p hr).2.trans hdensity) (by positivity)

theorem power_grid_radii {δ q : ℝ} {N : ℕ} (hq : 0 < q) (hqsmall : q ≤ 1 / 3)
    (hscale : q ^ N = δ) (j : Fin N) :
    0 < q ^ j.val ∧ q ^ j.val ≤ 1 ∧ δ ≤ q ^ j.val / 3 := by
  have hq1 : q ≤ 1 := by linarith
  refine ⟨pow_pos hq _, pow_le_one₀ hq.le hq1, ?_⟩
  have hh : δ ≤ q ^ (j.val + 1) := by
    rw [← hscale]
    exact pow_le_pow_of_le_one hq.le hq1 (Nat.succ_le_of_lt j.isLt)
  rw [pow_succ] at hh
  nlinarith [pow_nonneg hq.le j.val]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
