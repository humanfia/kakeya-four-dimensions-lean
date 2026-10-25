-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainOverlapCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainOverlapCount.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PrismOverlap
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainDilateCount

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume frozen_prism_convex)

noncomputable section

def grainOverlapConstant (τ : ℝ) : ℝ :=
  1000000 * ((4 * (48 / τ) + 44) ^ 2 * (48 / τ + 6)) ^ 2 * (48 / τ) ^ 3

theorem grainOverlapConstant_pos {τ : ℝ} (hτ : 0 < τ) : 0 < grainOverlapConstant τ := by
  unfold grainOverlapConstant
  positivity

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- Uniform density and coarse separation control the degree of the
positive-share overlap relation on selected grains. -/
theorem selected_overlap_count (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) {τ : ℝ} (hτ : 0 < τ) (i : Fin D.L) :
    ((D.Q.filter fun j => O (τ * (D.a * (ρ * c) * c)) <
      μ (P D.a (ρ * c) c (D.z i) (D.e i) ∩ P D.a (ρ * c) c (D.z j) (D.e j))).card : ℝ) ≤
        grainOverlapConstant τ * δ ^ (-(21 * ε / 40)) := by
  classical
  obtain ⟨ha, hρ, -, hc, -⟩ := D.dimensions hδ
  let R := D.Q.filter fun j => O (τ * (D.a * (ρ * c) * c)) <
    μ (P D.a (ρ * c) c (D.z i) (D.e i) ∩ P D.a (ρ * c) c (D.z j) (D.e j))
  have hvol (j : Fin D.L) : μ (P D.a (ρ * c) c (D.z j) (D.e j)) =
      O (D.a * (ρ * c) * c) := frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le _ _
  have hsub : ∀ j ∈ R, P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P ((48 / τ) * D.a) ((48 / τ) * (ρ * c)) ((48 / τ) * c) (D.z i) (D.e i) := by
    intro j hj
    apply convex_subset_prism_of_overlap (frozen_prism_convex _ _ _ _ _)
      (by rw [hvol]; exact ENNReal.ofReal_pos.mpr (by positivity))
      (by rw [hvol]; exact ENNReal.ofReal_ne_top) ha (mul_pos hρ hc) hc hτ
    rw [hvol, ← ENNReal.ofReal_mul hτ.le, inter_comm]
    exact (Finset.mem_filter.mp hj).2.le
  have hh := D.selected_dilation_count hδ (by positivity : 0 ≤ 48 / τ) R
    (Finset.filter_subset _ _) (D.z i) (D.e i) hsub
  change δ ^ (21 * ε / 40) * R.card ≤ grainOverlapConstant τ at hh
  change (R.card : ℝ) ≤ _
  calc
    _ ≤ grainOverlapConstant τ / δ ^ (21 * ε / 40) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr (by nlinarith only [hh])
    _ = _ := by rw [div_eq_mul_inv, Real.rpow_neg hδ.le]

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
