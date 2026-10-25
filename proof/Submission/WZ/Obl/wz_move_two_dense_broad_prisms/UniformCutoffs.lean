-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.UniformCutoffs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.RadiusPalette
import Submission.WZ.Obl.wz_broad_grains_initialization.PacketPower
import Submission.WZ.Obl.wz_horizontal_tube_exclusion.Vertical

/-! Common small-scale cutoffs, fixed before the tube data. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

/-- One cutoff pays all fixed constants, the Córdoba logarithm, and the common
dyadic radius/angle palette. -/
theorem uniform_geometric_cutoffs {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/100 ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
        (10:ℝ)^40*d^(η/4) ≤ 1 ∧
        (10:ℝ)^40*(1+Real.log (1/d))*d^(ε/2) ≤ 1 ∧
        ∃ K : ℕ, d ≤ (1/2:ℝ)^K ∧ (1/2:ℝ)^K < 2*d ∧
          d^(η/2) ≤ 1/(2*((K:ℝ)+1)) := by
  obtain ⟨ds, hds, hs⟩ := wz_move_two_long_grains_gain.small_rpow
    (by positivity : 0 < η/4) (by positivity : 0 < 1/(10:ℝ)^40)
  obtain ⟨dl, hdl, hl⟩ := wz_horizontal_tube_exclusion.exists_log_power_cutoff
    ((10:ℝ)^40) (by norm_num : (0:ℝ) < 1) (by positivity : 0 < ε/2)
  obtain ⟨dp, hdp, hdp100, hp⟩ := wz_broad_grains_initialization.angular_packet_power_budget
    (by positivity : 0 < η/2)
  refine ⟨min dp (min ds dl), lt_min hdp (lt_min hds hdl),
    (min_le_left _ _).trans hdp100, ?_⟩
  intro d hd hdd
  have hdp' := hdd.trans (min_le_left _ _)
  have hds' := (hdd.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdl' := (hdd.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsmall : (10:ℝ)^40*d^(η/4) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hs d hd hds') (by positivity : 0 ≤ (10:ℝ)^40)
    norm_num at hh ⊢
    exact hh
  have hd1 : d ≤ 1 := (hdp'.trans hdp100).trans (by norm_num)
  obtain ⟨K, hdK, hK2⟩ := wz_regular_transverse_affine_cells.exists_dyadic_bottom hd hd1
  exact ⟨hsmall, hl d hd hdl', K, hdK, hK2, (hp d hd hdp').2 K hdK⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
