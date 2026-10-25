-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PrismBridge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxGeometry
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

theorem orthonormal_boxAxis (e : V ≃ₗᵢ[ℝ] V) : Orthonormal ℝ (boxAxis e) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_boxAxis]
  simp only [boxAxis, e.apply_symm_apply, EuclideanSpace.basisFun_apply,
    PiLp.single_apply]

theorem frozen_prism_eq (a b : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P (2 * a) (2 * b) (1 / 500) z e = prism a b z (boxAxis e) := by
  ext p
  simp only [P, ι, prism, Set.mem_setOf_eq, inner_boxAxis]
  norm_num

/-- A common homothety puts arbitrary-length frozen grains in the fixed-length
prism convention used by the transverse filling library. -/
theorem frozen_prism_smul_membership {a b c r : ℝ} (hr : 0 < r)
    (hrc : r * c = 1 / 500) (z : V) (e : V ≃ₗᵢ[ℝ] V) (p : V) :
    p ∈ P a b c z e ↔
      r • p ∈ prism (r * a / 2) (r * b / 2) (r • z) (boxAxis e) := by
  have he (j : Fin 3) : inner ℝ (boxAxis e j) (r • p - r • z) = r * e (p - z) j := by
    rw [← smul_sub, inner_smul_right, inner_boxAxis]
  change (|e (p - z) 0| ≤ a / 2 ∧ |e (p - z) 1| ≤ b / 2 ∧ |e (p - z) 2| ≤ c / 2) ↔ _
  simp only [prism, Set.mem_setOf_eq, he, abs_mul, abs_of_pos hr]
  have h0 : r * |e (p - z) 0| ≤ r * a / 2 ↔ |e (p - z) 0| ≤ a / 2 := by
    rw [show r * a / 2 = r * (a / 2) by ring, mul_le_mul_iff_right₀ hr]
  have h1 : r * |e (p - z) 1| ≤ r * b / 2 ↔ |e (p - z) 1| ≤ b / 2 := by
    rw [show r * b / 2 = r * (b / 2) by ring, mul_le_mul_iff_right₀ hr]
  have h2 : r * |e (p - z) 2| ≤ 1 / 1000 ↔ |e (p - z) 2| ≤ c / 2 := by
    rw [show (1 / 1000 : ℝ) = r * (c / 2) by nlinarith [hrc], mul_le_mul_iff_right₀ hr]
  rw [h0, h1, h2]

theorem frozen_prism_smul_image {a b c r : ℝ} (hr : 0 < r)
    (hrc : r * c = 1 / 500) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    (fun p => r • p) '' P a b c z e =
      prism (r * a / 2) (r * b / 2) (r • z) (boxAxis e) := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (frozen_prism_smul_membership hr hrc z e p).mp hp
  · intro hq
    have he : r • (r⁻¹ • q) = q := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    refine ⟨r⁻¹ • q, ?_, he⟩
    apply (frozen_prism_smul_membership hr hrc z e (r⁻¹ • q)).mpr
    rwa [he]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
