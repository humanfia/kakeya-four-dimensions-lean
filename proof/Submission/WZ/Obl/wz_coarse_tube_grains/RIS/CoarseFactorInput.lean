-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.CoarseFactorInput.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.CoarseLocalization
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.FactorKT

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric

/-- Any unit tube of radius at most one meeting the unit ball lies in the ball of radius four. -/
theorem tube_subset_ball_four_of_meets {ρ : ℝ} (hρ : ρ ≤ 1) {y w : Space}
    (hw : ‖w‖ = 1) (hmeet : (Tube ρ y w ∩ ball 0 1).Nonempty) :
    Tube ρ y w ⊆ ball 0 4 := by
  obtain ⟨q, hqT, hqB⟩ := hmeet
  have hq : ‖q‖ < 1 := by simpa using hqB
  have hqc := tube_subset_midpoint_ball hw hqT
  change dist q (y + (1 / 2 : ℝ) • w) < ρ + 1 / 2 at hqc
  have hn := norm_le_norm_add_norm_sub q (y + (1 / 2 : ℝ) • w)
  rw [← dist_eq_norm] at hn
  have hcenter : ‖y + (1 / 2 : ℝ) • w‖ < ρ + 3 / 2 := by
    linarith
  intro p hp
  have hpc := tube_subset_midpoint_ball hw hp
  change dist p (y + (1 / 2 : ℝ) • w) < ρ + 1 / 2 at hpc
  have hn' := norm_le_norm_add_norm_sub (y + (1 / 2 : ℝ) • w) p
  rw [← dist_eq_norm, dist_comm (y + (1 / 2 : ℝ) • w)] at hn'
  apply mem_ball_zero_iff.mpr
  linarith

namespace Interfaces

/-- The coarse cover supplied by the grains decomposition satisfies the bounded-ambient
input of the existing Proposition 4.6 toolkit, without any extra containment assumption. -/
theorem c_factor_family {δ η m l h ρ : ℝ} {n N : ℕ}
    {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
    {y w : Fin N → V} {f : Fin n → Fin N}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (hA : A δ η m l n x v Y) (hC : C δ h n x v Y S Z ρ N y w f) :
    Factor.Fam 4 ρ y w := by
  refine ⟨hδ.trans_le hδρ, hρ1, hC.2.2.1, ?_⟩
  intro k
  exact tube_subset_ball_four_of_meets hρ1 (hC.2.2.1 k)
    (c_coarse_meets_unit_ball hδ hA hC k)

end Interfaces

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS
