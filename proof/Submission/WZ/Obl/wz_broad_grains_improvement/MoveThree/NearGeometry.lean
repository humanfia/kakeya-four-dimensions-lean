-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NearGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NearGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainCoefficient

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (boxAxis boxAxis_norm inner_boxAxis frozenBasis frozenBasis_apply)

noncomputable section

/-- Containment of natural plates bounds their normal-coordinate change in
both directions. The broad directions may rotate freely within the plate. -/
theorem near_plate_normal_coordinates {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V)
    (hnear : P a c c z e ⊆ P (2 * a) (2 * c) (2 * c) z₀ e₀) :
    ∀ j : Fin 3, j ≠ 0 → |e (boxAxis e₀ j) 0| ≤ 4 * a / c := by
  have hmem (j : Fin 3) (hj : j ≠ 0) (t : ℝ) (ht : |t| ≤ c / 2) :
      z + t • boxAxis e j ∈ P a c c z e := by
    simp only [P, ι, mem_ofPred_eq, add_sub_cancel_left, map_smul, PiLp.smul_apply,
      smul_eq_mul, boxAxis, LinearIsometryEquiv.apply_symm_apply]
    fin_cases j <;> simp_all [EuclideanSpace.basisFun_apply]
    <;> constructor <;> positivity
  have hlin (j : Fin 3) (t : ℝ) :
      e₀ (z + t • boxAxis e j - z₀) 0 = e₀ (z - z₀) 0 + t * e₀ (boxAxis e j) 0 := by
    rw [show z + t • boxAxis e j - z₀ = (z - z₀) + t • boxAxis e j by module,
      map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have haxis (j : Fin 3) (hj : j ≠ 0) : |e₀ (boxAxis e j) 0| ≤ 2 * a / c := by
    have hp := (hnear (hmem j hj (c / 2) (by rw [abs_of_pos (by positivity)]))).1
    have hm := (hnear (hmem j hj (-(c / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]))).1
    change |e₀ (z + (c / 2) • boxAxis e j - z₀) 0| ≤ 2 * a / 2 at hp
    change |e₀ (z + (-(c / 2)) • boxAxis e j - z₀) 0| ≤ 2 * a / 2 at hm
    rw [hlin] at hp hm
    have hh := (abs_sub (e₀ (z - z₀) 0 + (c / 2) * e₀ (boxAxis e j) 0)
      (e₀ (z - z₀) 0 + (-(c / 2)) * e₀ (boxAxis e j) 0)).trans (add_le_add hp hm)
    rw [show e₀ (z - z₀) 0 + c / 2 * e₀ (boxAxis e j) 0 -
      (e₀ (z - z₀) 0 + -(c / 2) * e₀ (boxAxis e j) 0) =
      c * e₀ (boxAxis e j) 0 by ring, abs_mul, abs_of_pos hc] at hh
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hcomm (i j : Fin 3) : e (boxAxis e₀ j) i = e₀ (boxAxis e i) j := by
    rw [← inner_boxAxis, ← inner_boxAxis, real_inner_comm]
  have hn := EuclideanSpace.real_norm_sq_eq (e₀ (boxAxis e 0))
  have hm := EuclideanSpace.real_norm_sq_eq (e (boxAxis e₀ 0))
  rw [e₀.norm_map, boxAxis_norm, Fin.sum_univ_three] at hn
  rw [e.norm_map, boxAxis_norm, Fin.sum_univ_three, hcomm 0 0, hcomm 1 0, hcomm 2 0] at hm
  have h1 := sq_le_sq₀ (abs_nonneg (e₀ (boxAxis e 1) 0)) (by positivity : 0 ≤ 2 * a / c)
  have h2 := sq_le_sq₀ (abs_nonneg (e₀ (boxAxis e 2) 0)) (by positivity : 0 ≤ 2 * a / c)
  have h1' := h1.mpr (haxis 1 (by decide))
  have h2' := h2.mpr (haxis 2 (by decide))
  rw [sq_abs] at h1' h2'
  have hsum : (e₀ (boxAxis e 0) 1) ^ 2 + (e₀ (boxAxis e 0) 2) ^ 2 ≤
      2 * (2 * a / c) ^ 2 := by linarith only [hn, hm, h1', h2']
  intro j hj
  rw [hcomm 0 j]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4 * a / c)).mp
  rw [sq_abs]
  rw [show (4 * a / c) ^ 2 = 4 * (2 * a / c) ^ 2 by ring]
  fin_cases j
  · exact False.elim (hj rfl)
  · exact (le_add_of_nonneg_right (sq_nonneg (e₀ (boxAxis e 0) 2))).trans
      (hsum.trans (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg (2 * a / c))))
  · exact (le_add_of_nonneg_left (sq_nonneg (e₀ (boxAxis e 0) 1))).trans
      (hsum.trans (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg (2 * a / c))))

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
