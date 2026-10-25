-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CoarseGrainContainer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CoarseGrainContainer.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainAxes
import Submission.WZ.Obl.wz_grains_nonsingular_slices.Nondegenerate

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm inner_boxAxis frozen_prism_ends grain_axis_close
    abs_inner_le_projective)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd pd_symm)

noncomputable section

/-- Coarse parents of grains in one fixed dilation lie in a common bounded
prism of transverse width proportional to the coarse radius. -/
theorem coarse_parent_of_grain_containment {a ρ c C : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 0 ≤ C) (hac : a ≤ ρ * c)
    (z z₀ y w : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (hw : ‖w‖ = 1)
    (hparent : P a (ρ * c) c z e ⊆ T ρ y w)
    (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2)
    (hsub : P a (ρ * c) c z e ⊆ P (C * a) (C * (ρ * c)) (C * c) z₀ e₀) :
    T ρ y w ⊆ P ((4 * C + 44) * ρ) ((4 * C + 44) * ρ) (C + 6) z₀ e₀ := by
  have hz : z ∈ P a (ρ * c) c z e := by
    simp only [P, ι, mem_ofPred_eq, sub_self, map_zero, PiLp.zero_apply, abs_zero]
    exact ⟨by positivity, by positivity, by positivity⟩
  have hzT := hparent hz
  have hzc := hsub hz
  have hshort (p : V) (hp : p ∈ P (C * a) (C * (ρ * c)) (C * c) z₀ e₀)
      (j : Fin 3) (hj : j ≠ 2) : |e₀ (p - z₀) j| ≤ C * (ρ * c) / 2 := by
    fin_cases j
    · exact hp.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hac hC])
    · exact hp.2.1
    · exact False.elim (hj rfl)
  have hlin (t : ℝ) (j : Fin 3) :
      e₀ (z + t • boxAxis e 2 - z₀) j =
        e₀ (z - z₀) j + t * e₀ (boxAxis e 2) j := by
    rw [show z + t • boxAxis e 2 - z₀ = (z - z₀) + t • boxAxis e 2 by module,
      map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hends := frozen_prism_ends ha.le (mul_pos hρ hc).le hc.le z e
  have haxis (j : Fin 3) (hj : j ≠ 2) : |e₀ (boxAxis e 2) j| ≤ C * ρ := by
    have hp := hshort _ (hsub hends.1) j hj
    have hm' : z + (-(c / 2)) • boxAxis e 2 ∈ P a (ρ * c) c z e := by
      simpa only [neg_smul, sub_eq_add_neg] using hends.2
    have hm := hshort _ (hsub hm') j hj
    rw [hlin] at hp hm
    have hh := (abs_sub (e₀ (z - z₀) j + (c / 2) * e₀ (boxAxis e 2) j)
      (e₀ (z - z₀) j + (-(c / 2)) * e₀ (boxAxis e 2) j)).trans (add_le_add hp hm)
    rw [show e₀ (z - z₀) j + c / 2 * e₀ (boxAxis e 2) j -
      (e₀ (z - z₀) j + -(c / 2) * e₀ (boxAxis e 2) j) =
      c * e₀ (boxAxis e 2) j by ring, abs_mul, abs_of_pos hc] at hh
    calc
      _ ≤ (C * (ρ * c)) / c := (le_div_iff₀ hc).mpr (by nlinarith only [hh])
      _ = C * ρ := by field_simp
  have hang := grain_axis_close hρ.le e hw halign
  have hdir (j : Fin 3) (hj : j ≠ 2) : |e₀ w j| ≤ (C + 20) * ρ := by
    have hh := abs_inner_le_projective w (boxAxis e 2) (boxAxis e₀ j)
    rw [real_inner_comm (boxAxis e₀ j) w, real_inner_comm (boxAxis e₀ j) (boxAxis e 2), inner_boxAxis,
      inner_boxAxis, boxAxis_norm, mul_one] at hh
    change |e₀ w j| ≤ |e₀ (boxAxis e 2) j| + pd w (boxAxis e 2) at hh
    rw [pd_symm] at hh
    nlinarith [haxis j hj]
  have hdir2 : |e₀ w 2| ≤ 1 := by
    simpa only [Real.norm_eq_abs, e₀.norm_map, hw] using PiLp.norm_apply_le (e₀ w) 2
  have hcenter (j : Fin 3) (hj : j ≠ 2) : |e₀ (z - z₀) j| ≤ C * ρ / 2 := by
    exact (hshort _ hzc j hj).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hC hρ.le)])
  have hcenter2 : |e₀ (z - z₀) 2| ≤ C / 2 :=
    hzc.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hc1 hC])
  intro p hp
  have hslab (j : Fin 3) (d : ℝ) (hd : |e₀ (z - z₀) j| ≤ d) :
      |e₀ (p - z₀) j| ≤ 2 * ρ + |e₀ w j| + d := by
    have hz' : |inner ℝ (boxAxis e₀ j) z - inner ℝ (boxAxis e₀ j) z₀| ≤ d := by
      rwa [← inner_sub_right, inner_boxAxis]
    have hh := WangZahlLot.Obl.wz_grains_nonsingular_slices.nd_tube_slab
      (by rw [boxAxis_norm] : ‖boxAxis e₀ j‖ ≤ 1) hzT hz' hp
    simpa only [inner_boxAxis, map_sub, PiLp.sub_apply] using hh
  refine ⟨?_, ?_, ?_⟩
  · have hh := hslab 0 _ (hcenter 0 (by decide))
    have hd := hdir 0 (by decide)
    change |e₀ (p - z₀) 0| ≤ ((4 * C + 44) * ρ) / 2
    nlinarith [mul_nonneg hC hρ.le]
  · have hh := hslab 1 _ (hcenter 1 (by decide))
    have hd := hdir 1 (by decide)
    change |e₀ (p - z₀) 1| ≤ ((4 * C + 44) * ρ) / 2
    nlinarith [mul_nonneg hC hρ.le]
  · have hh := hslab 2 _ hcenter2
    change |e₀ (p - z₀) 2| ≤ (C + 6) / 2
    linarith

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
