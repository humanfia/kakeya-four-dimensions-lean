-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.SlopeDirections.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.CartesianFrostman
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.IndexedDirections

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

attribute [local instance] Classical.propDecidable

noncomputable def unitSlope (t : ℝ) : Plane :=
  ‖cartesianPoint (1, t)‖⁻¹ • cartesianPoint (1, t)

theorem slope_vector_norm (t : ℝ) : 1 ≤ ‖cartesianPoint (1, t)‖ := by
  have h := PiLp.norm_apply_le (cartesianPoint (1, t)) 0
  simpa [cartesianPoint] using h

theorem slope_vector_norm_upper {t : ℝ} (ht : |t| ≤ 1) :
    ‖cartesianPoint (1, t)‖ ≤ 2 := by
  have hs : ‖cartesianPoint (1, t)‖ ^ 2 = 1 + t ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, cartesianPoint]
  have hsq : t ^ 2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
  nlinarith [norm_nonneg (cartesianPoint (1, t))]

theorem unitSlope_norm (t : ℝ) : ‖unitSlope t‖ = 1 := by
  have hn : 0 < ‖cartesianPoint (1, t)‖ := zero_lt_one.trans_le (slope_vector_norm t)
  simp [unitSlope, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']

theorem unitSlope_zero (t : ℝ) : unitSlope t 0 = ‖cartesianPoint (1, t)‖⁻¹ := by
  simp [unitSlope, cartesianPoint]

theorem unitSlope_one (t : ℝ) : unitSlope t 1 = ‖cartesianPoint (1, t)‖⁻¹ * t := by
  simp [unitSlope, cartesianPoint]

theorem slope_dist_le {s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    dist s t ≤ 4 * dist (unitSlope s) (unitSlope t) := by
  have hsn : 0 < ‖cartesianPoint (1, s)‖ := zero_lt_one.trans_le (slope_vector_norm s)
  have htn : 0 < ‖cartesianPoint (1, t)‖ := zero_lt_one.trans_le (slope_vector_norm t)
  have hid : (‖cartesianPoint (1, s)‖ * ‖cartesianPoint (1, t)‖) *
      inner ℝ (unitSlope s) (perp (unitSlope t)) = s - t := by
    rw [plane_inner]
    simp only [perp, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, unitSlope_zero, unitSlope_one]
    field_simp
    <;> ring
  have hi : |inner ℝ (unitSlope s) (perp (unitSlope t))| ≤
      dist (unitSlope s) (unitSlope t) := by
    have heq : inner ℝ (unitSlope s) (perp (unitSlope t)) =
        inner ℝ (unitSlope s - unitSlope t) (perp (unitSlope t)) := by
      rw [inner_sub_left, perp_inner, sub_zero]
    rw [heq]
    simpa only [perp_norm, unitSlope_norm, mul_one, dist_eq_norm] using
      abs_real_inner_le_norm (unitSlope s - unitSlope t) (perp (unitSlope t))
  have hnprod : ‖cartesianPoint (1, s)‖ * ‖cartesianPoint (1, t)‖ ≤ 4 := by
    nlinarith [slope_vector_norm_upper hs, slope_vector_norm_upper ht]
  rw [Real.dist_eq, ← hid, abs_mul, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans
    (mul_le_mul_of_nonneg_right hnprod dist_nonneg)

def IndexedRealFrostman {I : Type*} [Fintype I] (δ C : ℝ) (t : I → ℝ) : Prop :=
  ∀ x r : ℝ, δ ≤ r →
    ((Finset.univ.filter (fun i => dist (t i) x ≤ r)).card : ℝ) ≤
      C * r * (Fintype.card I : ℝ)

theorem indexedFrostman_unitSlope {I : Type*} [Fintype I] {δ C : ℝ} {t : I → ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (ht : ∀ i, |t i| ≤ 1)
    (hf : IndexedRealFrostman δ C t) :
    IndexedFrostman δ (8 * C) (fun i => unitSlope (t i)) := by
  classical
  intro z r hr
  have hrp : 0 < r := hδ.trans_le hr
  let S := Finset.univ.filter (fun i => dist (unitSlope (t i)) z ≤ r)
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hsub : S ⊆ Finset.univ.filter (fun i => dist (t i) (t i₀) ≤ 8 * r) := by
      intro i hi
      have hdi := (Finset.mem_filter.mp hi).2
      have hdi₀ := (Finset.mem_filter.mp hi₀).2
      have hdist : dist (unitSlope (t i)) (unitSlope (t i₀)) ≤ 2 * r := by
        have hh := dist_triangle (unitSlope (t i)) z (unitSlope (t i₀))
        rw [dist_comm z (unitSlope (t i₀))] at hh
        linarith
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (slope_dist_le (ht i) (ht i₀)).trans (by linarith)⟩
    have hc : (S.card : ℝ) ≤
        ((Finset.univ.filter (fun i => dist (t i) (t i₀) ≤ 8 * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact (hc.trans (hf (t i₀) (8 * r) (by linarith))).trans_eq (by ring)
  · change (S.card : ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
    positivity

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
