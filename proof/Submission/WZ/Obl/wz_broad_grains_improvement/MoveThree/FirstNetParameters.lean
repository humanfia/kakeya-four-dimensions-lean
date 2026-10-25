-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FirstNetParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FirstNetParameters.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 8a2b46b, FirstNetParameters.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SummedNet
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.CapComparison
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open WangZahlLot.Obl.wz_transverse_cell_weighted_cover (netConst netConst_pos)

/-- The balancing depth is fixed before delta. One cutoff pays that depth,
the cardinality condition, and the aggregate cap comparison for every block. -/
theorem first_net_parameters {A u ζ σ ε t ell β uc Ccap Csat H : ℝ}
    (hA : 0 < A) (hu : 0 < u) (hζ : 0 < ζ)
    (hCcap : 0 ≤ Ccap) (hCsat : 0 ≤ Csat) (hH : 0 < H)
    (hgap : ε + u + t + ell + β + uc < ζ * σ / 4) :
    ∃ (d : ℕ) (d₀ : ℝ), 0 < d ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        1 < δ ^ (-u) ∧ 1 ≤ δ ^ (-ζ / 2) ∧ δ ^ u * d ≤ netConst ∧
        (∀ n : ℕ, (n : ℝ) ≤ δ ^ (-100 : ℝ) → (n : ℝ) < (δ ^ (-u)) ^ d) ∧
        64 * Ccap * Csat * H < (A * netConst / d) *
          δ ^ (ε + u + t + ell + β + uc - ζ * σ / 4) := by
  obtain ⟨d, hd⟩ := exists_nat_gt (100 / u)
  have hdR : (0 : ℝ) < d := (by positivity : 0 < 100 / u).trans hd
  have hdN : 0 < d := Nat.cast_pos.mp hdR
  have hdu : 100 < u * d := by nlinarith [(div_lt_iff₀ hu).mp hd]
  have hnet : 0 < netConst := netConst_pos
  obtain ⟨dC, hdC, _, HC⟩ := aggregate_cap_comparison_cutoff Ccap Csat H
    (A * netConst / d) (ζ * σ / 4 - (ε + u + t + ell + β + uc))
    hCcap hCsat hH (by positivity) (sub_pos.mpr hgap)
  obtain ⟨dR, hdR0, HR⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hu (by positivity : 0 < netConst / d)
  refine ⟨d, min (1 / 100) (min dC dR), hdN, by positivity, min_le_left _ _, ?_⟩
  intro δ hδ hδd
  have hδsmall : δ ≤ 1 / 100 := hδd.trans (min_le_left _ _)
  have hδ1 : δ < 1 := hδsmall.trans_lt (by norm_num)
  have hδC : δ ≤ dC := hδd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδR : δ ≤ dR := hδd.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ hδ1 (neg_neg_of_pos hu),
    ?_, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le
      (show -ζ / 2 ≤ 0 by linarith)
  · exact (le_div_iff₀ hdR).mp (HR δ hδ hδR)
  · intro n hn
    calc
      _ ≤ δ ^ (-100 : ℝ) := hn
      _ < δ ^ (-u * d) := Real.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
      _ = _ := by rw [Real.rpow_mul hδ.le, Real.rpow_natCast]
  · exact HC δ hδ hδC _ (by linarith)

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
