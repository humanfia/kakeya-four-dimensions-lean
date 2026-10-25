-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.Anisotropic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TransverseStrips

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

/-- A diagonal map in the orthogonal frame given by a unit vector and its
perpendicular. The two scale factors will be exchanged for dual inputs. -/
noncomputable def anisotropicMap (e : Plane) (p q : ℝ) (x : Plane) : Plane :=
  (p * inner ℝ x e) • e + (q * inner ℝ x (perp e)) • perp e

theorem unit_inner_decomposition {e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    inner ℝ x e • e + inner ℝ x (perp e) • perp e = x := by
  have hee : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    calc e 0 ^ 2 + e 1 ^ 2 = inner ℝ e e := by rw [plane_inner]; ring
      _ = ‖e‖ ^ 2 := real_inner_self_eq_norm_sq e
      _ = 1 := by rw [he]; norm_num
  ext i
  fin_cases i <;> simp [plane_inner, perp] <;>
    nlinarith [congrArg (fun z : ℝ => x 0 * z) hee, congrArg (fun z : ℝ => x 1 * z) hee]

theorem anisotropicMap_inner {e : Plane} (he : ‖e‖ = 1) (p q : ℝ) (x : Plane) :
    inner ℝ (anisotropicMap e p q x) e = p * inner ℝ x e ∧
      inner ℝ (anisotropicMap e p q x) (perp e) = q * inner ℝ x (perp e) := by
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hpp : inner ℝ (perp e) (perp e) = 1 := by
    rw [real_inner_self_eq_norm_sq, perp_norm, he]; norm_num
  have hpe : inner ℝ (perp e) e = 0 := by rw [real_inner_comm, perp_inner]
  simp only [anisotropicMap, inner_add_left, real_inner_smul_left, hee, hpp,
    hpe, perp_inner, mul_zero, zero_add, add_zero, mul_one, and_self]

theorem anisotropicMap_sub (e : Plane) (p q : ℝ) (x y : Plane) :
    anisotropicMap e p q (x - y) = anisotropicMap e p q x - anisotropicMap e p q y := by
  simp only [anisotropicMap, inner_sub_left, mul_sub, sub_smul]
  abel

theorem anisotropicMap_norm_sq {e : Plane} (he : ‖e‖ = 1) (p q : ℝ) (x : Plane) :
    ‖anisotropicMap e p q x‖ ^ 2 =
      (p * inner ℝ x e) ^ 2 + (q * inner ℝ x (perp e)) ^ 2 := by
  have h := inner_sq_add_perp_inner_sq (anisotropicMap e p q x) e
  rw [(anisotropicMap_inner he p q x).1, (anisotropicMap_inner he p q x).2,
    he, one_pow, mul_one] at h
  exact h.symm

theorem anisotropicMap_norm_lower {e : Plane} (he : ‖e‖ = 1)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (x : Plane) :
    ‖x‖ ≤ ‖anisotropicMap e p q x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [anisotropicMap_norm_sq he]
  have hid := inner_sq_add_perp_inner_sq x e
  rw [he, one_pow, mul_one] at hid
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hp2 (sq_nonneg (inner ℝ x e)),
    mul_le_mul_of_nonneg_right hq2 (sq_nonneg (inner ℝ x (perp e)))]

theorem anisotropicMap_dist_lower {e : Plane} (he : ‖e‖ = 1)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (x y : Plane) :
    dist x y ≤ dist (anisotropicMap e p q x) (anisotropicMap e p q y) := by
  simpa only [dist_eq_norm, ← anisotropicMap_sub] using anisotropicMap_norm_lower he hp hq (x - y)

theorem anisotropicMap_injective {e : Plane} (he : ‖e‖ = 1)
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) : Function.Injective (anisotropicMap e p q) := by
  intro x y hxy
  have h := anisotropicMap_dist_lower he hp hq x y
  rw [hxy, dist_self] at h
  exact dist_eq_zero.mp (le_antisymm h dist_nonneg)

theorem anisotropicMap_norm_upper {e : Plane} (he : ‖e‖ = 1) (p q : ℝ) (x : Plane) :
    ‖anisotropicMap e p q x‖ ≤ |p * inner ℝ x e| + |q * inner ℝ x (perp e)| := by
  exact (norm_add_le _ _).trans_eq (by
    simp only [norm_smul, Real.norm_eq_abs, he, perp_norm, mul_one])

theorem inner_eq_frame_sum {e : Plane} (he : ‖e‖ = 1) (x y : Plane) :
    inner ℝ x y = inner ℝ x e * inner ℝ y e +
      inner ℝ x (perp e) * inner ℝ y (perp e) := by
  calc inner ℝ x y = inner ℝ x (inner ℝ y e • e + inner ℝ y (perp e) • perp e) := by
        rw [unit_inner_decomposition he]
    _ = _ := by rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]; ring

theorem anisotropicMap_dual_inner {e : Plane} (he : ‖e‖ = 1) (p q : ℝ) (x y : Plane) :
    inner ℝ (anisotropicMap e p q x) (anisotropicMap e q p y) = p * q * inner ℝ x y := by
  rw [inner_eq_frame_sum he, (anisotropicMap_inner he p q x).1,
    (anisotropicMap_inner he p q x).2, (anisotropicMap_inner he q p y).1,
    (anisotropicMap_inner he q p y).2, inner_eq_frame_sum he x y]
  ring

theorem anisotropicMap_dual_dot {e : Plane} (he : ‖e‖ = 1) {w : ℝ} (hw : 0 < w)
    (a b c : Plane) :
    inner ℝ a (b - c) = w * inner ℝ (anisotropicMap e w⁻¹ 1 a)
      (anisotropicMap e 1 w⁻¹ b - anisotropicMap e 1 w⁻¹ c) := by
  rw [← anisotropicMap_sub, anisotropicMap_dual_inner he]
  field_simp

end WangZahlLot.Obl.wz_separated_projection_dichotomy
