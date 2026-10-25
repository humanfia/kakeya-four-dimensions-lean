-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AnisotropicNormal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Anisotropic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem anisotropicMap_self_adjoint {e : Plane} (he : ‖e‖ = 1) (p q : ℝ) (x y : Plane) :
    inner ℝ (anisotropicMap e p q x) y = inner ℝ x (anisotropicMap e p q y) := by
  rw [inner_eq_frame_sum he, inner_eq_frame_sum he x (anisotropicMap e p q y),
    (anisotropicMap_inner he p q x).1, (anisotropicMap_inner he p q x).2,
    (anisotropicMap_inner he p q y).1, (anisotropicMap_inner he p q y).2]
  ring

theorem anisotropicMap_norm_upper_scale {e : Plane} (he : ‖e‖ = 1)
    {p q A : ℝ} (hp : |p| ≤ A) (hq : |q| ≤ A) (hA : 0 ≤ A) (x : Plane) :
    ‖anisotropicMap e p q x‖ ≤ A * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [anisotropicMap_norm_sq he]
  have hid := inner_sq_add_perp_inner_sq x e
  rw [he, one_pow, mul_one] at hid
  have hp2 : p ^ 2 ≤ A ^ 2 := (sq_le_sq).mpr (by simpa only [abs_of_nonneg hA] using hp)
  have hq2 : q ^ 2 ≤ A ^ 2 := (sq_le_sq).mpr (by simpa only [abs_of_nonneg hA] using hq)
  nlinarith [mul_le_mul_of_nonneg_right hp2 (sq_nonneg (inner ℝ x e)),
    mul_le_mul_of_nonneg_right hq2 (sq_nonneg (inner ℝ x (perp e)))]

theorem anisotropic_normal_bounds {e n : Plane} {h : ℝ}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    1 ≤ ‖anisotropicMap e 1 h⁻¹ n‖ ∧ ‖anisotropicMap e 1 h⁻¹ n‖ ≤ h⁻¹ ∧
      |inner ℝ n (perp e)| ≤ h * ‖anisotropicMap e 1 h⁻¹ n‖ := by
  have hhinv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hn] using anisotropicMap_norm_lower he le_rfl hhinv n
  · simpa only [hn, mul_one] using anisotropicMap_norm_upper_scale he
      (by simpa only [abs_one] using hhinv) (le_of_eq (abs_of_pos (inv_pos.mpr hh)))
      (inv_nonneg.mpr hh.le) n
  · have hi := abs_real_inner_le_norm (anisotropicMap e 1 h⁻¹ n) (perp e)
    rw [(anisotropicMap_inner he 1 h⁻¹ n).2, abs_mul, abs_of_pos (inv_pos.mpr hh),
      perp_norm, he, mul_one] at hi
    have hs := mul_le_mul_of_nonneg_left hi hh.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] using hs

/-- Pullback of a unit-normal strip under the expanding diagonal map. -/
theorem anisotropic_strip_pullback {e n : Plane} {h : ℝ}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hh : 0 < h) (hh1 : h ≤ 1) (c r : ℝ) :
    ∃ u : Plane, ‖u‖ = 1 ∧ ∀ x : Plane,
      (|inner ℝ (anisotropicMap e 1 h⁻¹ x) n - c| < r ↔
        |inner ℝ x u - c / ‖anisotropicMap e 1 h⁻¹ n‖| < r / ‖anisotropicMap e 1 h⁻¹ n‖) := by
  let v := anisotropicMap e 1 h⁻¹ n
  have hv : 0 < ‖v‖ := zero_lt_one.trans_le (anisotropic_normal_bounds he hn hh hh1).1
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hv.le), hv.ne']
  refine ⟨u, hu, ?_⟩
  intro x
  have hid : |inner ℝ x u - c / ‖v‖| = |inner ℝ (anisotropicMap e 1 h⁻¹ x) n - c| / ‖v‖ := by
    dsimp [u]
    rw [real_inner_smul_right, show ‖v‖⁻¹ * inner ℝ x v - c / ‖v‖ = (inner ℝ x v - c) / ‖v‖ by ring,
      abs_div, abs_of_pos hv, anisotropicMap_self_adjoint he]
  change _ ↔ |inner ℝ x u - c / ‖v‖| < r / ‖v‖
  rw [hid]
  exact (div_lt_div_iff_of_pos_right hv).symm

end WangZahlLot.Obl.wz_separated_projection_dichotomy
