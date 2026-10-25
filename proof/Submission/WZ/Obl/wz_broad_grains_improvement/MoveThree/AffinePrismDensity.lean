-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.AffinePrismDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/AffinePrismDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (affine_ball_density_mass_in_box frozen_prism_box frozenBasis)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

/-- A physical ball-density bound transfers to an affine prism whenever
the image of the ball fits its short side. -/
theorem affine_prism_density_upper {a b c r lam L J : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hr : 0 < r)
    (hL : 0 ≤ L) (hfit : L * r ≤ a / 2) (hlam : 0 ≤ lam) (hJ : 0 ≤ J)
    (f : V ≃ᵃ[ℝ] V) (z : V) (e : V ≃ₗᵢ[ℝ] V) (F U : Set V)
    (hvol : ∀ W, μ (f '' W) = O J * μ W)
    (hLip : ∀ p q, dist (f p) (f q) ≤ L * dist p q)
    (hFU : F ⊆ U) (hUball : U ⊆ ball (0 : V) 1)
    (hbox : f '' F ⊆ P a b c z e)
    (hupper : ∀ p ∈ F, μ (U ∩ ball p r) ≤ O (lam * r ^ 3)) :
    μ (f '' F) ≤ O (512 * lam * (a * b * c)) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hTB : TotallyBounded F := (isCompact_closedBall (0 : V) 1).totallyBounded.subset
    ((hFU.trans hUball).trans ball_subset_closedBall)
  have hbox' : F ⊆ f.symm '' orthogonalBox ![a / 2, b / 2, c / 2] z (frozenBasis e) := by
    intro p hp
    refine ⟨f p, ?_, f.symm_apply_apply p⟩
    rw [← frozen_prism_box]
    exact hbox (mem_image_of_mem f hp)
  have hh := affine_ball_density_mass_in_box hr hL hTB hFU f.symm
    ![a / 2, b / 2, c / 2] z (frozenBasis e) hLip hbox' hupper
  have hsub : orthogonalBox (fun j => (![a / 2, b / 2, c / 2] : Fin 3 → ℝ) j + L * r)
      z (frozenBasis e) ⊆ orthogonalBox ![a, b, c] z (frozenBasis e) := by
    intro p hp j
    have hj := hp j
    fin_cases j <;> norm_num at hj ⊢ <;> linarith
  have hmass : μ (f '' F) ≤ O (64 * lam) * μ (orthogonalBox ![a, b, c] z (frozenBasis e)) := by
    calc
      _ = O J * μ F := hvol F
      _ ≤ O J * (O (64 * lam) * μ (f.symm '' orthogonalBox
          (fun j => (![a / 2, b / 2, c / 2] : Fin 3 → ℝ) j + L * r) z (frozenBasis e))) :=
        mul_le_mul' le_rfl hh
      _ = O (64 * lam) * μ (orthogonalBox
          (fun j => (![a / 2, b / 2, c / 2] : Fin 3 → ℝ) j + L * r) z (frozenBasis e)) := by
        rw [mul_left_comm, ← hvol, image_image]
        simp
      _ ≤ _ := mul_le_mul' le_rfl (measure_mono hsub)
  apply hmass.trans_eq
  change O (64 * lam) * volume (orthogonalBox ![a, b, c] z (frozenBasis e)) = _
  rw [volume_orthogonalBox]
  · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * lam)]
    congr 1
    norm_num [Fin.prod_univ_three]
    ring
  · intro j
    fin_cases j <;> simp <;> positivity

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
