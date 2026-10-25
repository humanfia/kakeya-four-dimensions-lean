-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConvexWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConvexWidth.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_flat_factored_improvement.PairWidth
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismBridge

/- Adapted from the internal o169 branch x0551, commit 62ddc22,
   as advertised in the 2026-10-13 06:00Z API post. -/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (norm_sq_coords)

/-- A transverse coordinate gives a quantitative two-dimensional span. -/
theorem coordinate_pair_lower_scaled {v : V} {D : ℝ}
    (hD : 0 < D) (hD1 : D ≤ 1) (hv0 : |v 0| ≤ 1)
    {j : Fin 3} (hj : j ≠ 0) (hvj : D ≤ |v j|) (s t : ℝ) :
    (D / 2) * |s| ≤ ‖s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v‖ ∧
    (D / 2) * |t| ≤ ‖s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v‖ := by
  let p := s • EuclideanSpace.basisFun (Fin 3) ℝ 0 + t • v
  have hp0 : p 0 = s + t * v 0 := by simp [p, EuclideanSpace.basisFun_apply]
  have hpj : p j = t * v j := by
    simp [p, EuclideanSpace.basisFun_apply, EuclideanSpace.single, hj]
  have h0 : |p 0| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have hj' : |p j| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p j
  have ht : D * |t| ≤ ‖p‖ := by
    rw [hpj, abs_mul] at hj'
    nlinarith [mul_le_mul_of_nonneg_left hvj (abs_nonneg t)]
  have hs : |s| ≤ ‖p‖ + |t| := by
    have habs := abs_sub (s + t * v 0) (t * v 0)
    rw [add_sub_cancel_right, abs_mul] at habs
    rw [hp0] at h0
    nlinarith [mul_le_mul_of_nonneg_left hv0 (abs_nonneg t)]
  have hmul := mul_le_mul_of_nonneg_left hs hD.le
  have hnorm := mul_le_mul_of_nonneg_right hD1 (norm_nonneg p)
  exact ⟨by dsimp [p] at *; nlinarith, by dsimp [p] at *; nlinarith [norm_nonneg p]⟩

/-- Convexity propagates an interior ball to the middle half of a long chord. -/
theorem convex_middle_ball {U : Set V} (hU : Convex ℝ U) {x q : V} {r : ℝ}
    (hr : 0 < r) (hball : ball x r ⊆ U) (hq : q ∈ U)
    {t : ℝ} (ht : |t| ≤ 1 / 4) {z : V} (hz : ‖z‖ < r / 4) :
    x + (1 / 2 + t) • (q - x) + z ∈ U := by
  let a : ℝ := 1 / 2 - t
  have ha : 0 < a := by dsimp [a]; linarith [(abs_le.mp ht).2]
  have ha4 : 1 / 4 ≤ a := by dsimp [a]; linarith [(abs_le.mp ht).2]
  have hb : 0 ≤ 1 / 2 + t := by linarith [(abs_le.mp ht).1]
  have hp : x + a⁻¹ • z ∈ ball x r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ha)]
    rw [← div_eq_inv_mul, div_lt_iff₀ ha]
    exact hz.trans_le (by nlinarith)
  have h := hU (hball hp) hq ha.le hb (by dsimp [a]; ring)
  convert h using 1
  rw [smul_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  dsimp [a]
  module

/-- A long convex body with an interior radius `r`, contained in a thin prism,
has middle width comparable to `r/a` after the prism is normalized. -/
theorem normalized_convex_width {U : Set V} {a b r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (haSmall : a ≤ 1 / 64)
    (hr : 0 < r) (hra : r ≤ a) (hU : Convex ℝ U)
    (x z : V) (e : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ p i, f p i = (![a⁻¹, b⁻¹, 1 / 4] : Fin 3 → ℝ) i * e (p - z) i)
    (hball : ball x r ⊆ U) (hbox : U ⊆ P a b 4 z e)
    (hlong : ∃ p ∈ U, ∃ q ∈ U, (1 / 4 : ℝ) ≤ dist p q) :
    WideSection (f '' U) (r / (8192 * a)) := by
  have hx : x ∈ U := hball (mem_ball_self hr)
  obtain ⟨p, hp, q, hq, hpq⟩ := hlong
  have hfar : ∃ q ∈ U, (1 / 8 : ℝ) ≤ dist q x := by
    by_cases hpx : (1 / 8 : ℝ) ≤ dist p x
    · exact ⟨p, hp, hpx⟩
    · exact ⟨q, hq, by have htri := dist_triangle p x q; rw [dist_comm x q] at htri; linarith⟩
  obtain ⟨q, hq, hqx⟩ := hfar
  let v := f q - f x
  let w := e (q - x)
  have he : e (q - z) - e (x - z) = w := by dsimp [w]; rw [← map_sub]; congr 1; abel
  have hw0 : |w 0| ≤ a := by
    rw [← he]
    change |e (q - z) 0 - e (x - z) 0| ≤ a
    exact (abs_sub _ _).trans (by linarith [(hbox hq).1, (hbox hx).1])
  have hv (i : Fin 3) : v i = (![a⁻¹, b⁻¹, 1 / 4] : Fin 3 → ℝ) i * w i := by
    dsimp [v]
    change f q i - f x i = _
    rw [hf, hf, ← mul_sub]
    exact congrArg (fun u : V => (![a⁻¹, b⁻¹, 1 / 4] : Fin 3 → ℝ) i * u i) he
  have hv0 : |v 0| ≤ 1 := by
    rw [hv]
    change |a⁻¹ * w 0| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left hw0 (inv_nonneg.mpr ha.le)
      _ = _ := inv_mul_cancel₀ ha.ne'
  have hwlen : (1 / 8 : ℝ) ≤ ‖w‖ := by
    dsimp only [w]
    rw [e.norm_map]
    exact hqx
  have hw12 : (1 / 32 : ℝ) ≤ |w 1| ∨ (1 / 32 : ℝ) ≤ |w 2| := by
    by_contra hn
    push Not at hn
    have hsq0 := sq_le_sq' (abs_le.mp hw0).1 (abs_le.mp hw0).2
    have hsq1 := sq_le_sq' (abs_le.mp hn.1.le).1 (abs_le.mp hn.1.le).2
    have hsq2 := sq_le_sq' (abs_le.mp hn.2.le).1 (abs_le.mp hn.2.le).2
    nlinarith [norm_sq_coords w]
  have hvj : ∃ j : Fin 3, j ≠ 0 ∧ (1 / 128 : ℝ) ≤ |v j| := by
    rcases hw12 with hw1 | hw2
    · refine ⟨1, by decide, ?_⟩
      rw [hv]
      change (1 / 128 : ℝ) ≤ |b⁻¹ * w 1|
      rw [abs_mul, abs_of_pos (inv_pos.mpr (ha.trans_le hab))]
      have hi : (1 / 4 : ℝ) ≤ b⁻¹ := by
        rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) (ha.trans_le hab)]
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hi (abs_nonneg (w 1))]
    · refine ⟨2, by decide, ?_⟩
      rw [hv]
      change (1 / 128 : ℝ) ≤ |(1 / 4) * w 2|
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      linarith
  obtain ⟨j, hj, hjv⟩ := hvj
  let e₀ := EuclideanSpace.basisFun (Fin 3) ℝ 0
  let ξ := e.symm e₀
  have hξ : ‖ξ‖ = 1 := by simp [ξ, e₀]
  have hflinear (u : V) (i : Fin 3) : f.linear u i =
      (![a⁻¹, b⁻¹, 1 / 4] : Fin 3 → ℝ) i * e u i := by
    have hh := f.map_vadd z u
    simp only [vadd_eq_add] at hh
    have hi := congrArg (fun p : V => p i) hh
    change f (u + z) i = f.linear u i + f z i at hi
    rw [hf, hf] at hi
    simpa only [add_sub_cancel_right, sub_self, map_zero, WithLp.ofLp_zero,
      Pi.zero_apply, mul_zero, add_zero] using hi.symm
  have hfξ : f.linear ξ = a⁻¹ • e₀ := by
    ext i
    rw [hflinear]
    dsimp only [ξ]
    rw [e.apply_symm_apply]
    fin_cases i <;> simp [e₀, EuclideanSpace.basisFun_apply]
  have hfv : f.linear (q - x) = v := by
    apply eq_sub_iff_add_eq.mpr
    exact (show f q = f.linear (q - x) + f x by
      simpa only [vadd_eq_add, sub_add_cancel] using f.map_vadd x (q - x)).symm
  have hdiamond : ∀ s t : ℝ, |s| + |t| ≤ r / (16 * a) →
      f (x + (1 / 2 : ℝ) • (q - x)) + s • e₀ + t • v ∈ f '' U := by
    intro s t hst
    have hs : |s| ≤ r / (16 * a) := by linarith [abs_nonneg t]
    have ht : |t| ≤ 1 / 4 := by
      have hratio : r / (16 * a) ≤ 1 / 16 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith [abs_nonneg s]
    have hz : ‖(a * s) • ξ‖ < r / 4 := by
      rw [norm_smul, hξ, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos ha]
      have hh := (le_div_iff₀ (by positivity : 0 < 16 * a)).mp hs
      nlinarith
    let p := x + (1 / 2 + t) • (q - x) + (a * s) • ξ
    refine ⟨p, convex_middle_ball hU hr hball hq ht hz, ?_⟩
    have hp : p = (x + (1 / 2 : ℝ) • (q - x)) + (s • (a • ξ) + t • (q - x)) := by
      dsimp [p]; module
    rw [hp]
    have hmap (p u : V) : f (p + u) = f p + f.linear u := by
      simpa only [vadd_eq_add, add_comm] using f.map_vadd p u
    rw [hmap, f.linear.map_add, f.linear.map_smul, f.linear.map_smul,
      f.linear.map_smul, hfξ, hfv, smul_smul]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ ha.ne', mul_one]
    abel
  have H := wideSection_of_pair (by positivity : 0 ≤ r / (16 * a))
    (by norm_num : (0 : ℝ) ≤ (1 / 128) / 2)
    (f (x + (1 / 2 : ℝ) • (q - x))) e₀ v
    (coordinate_pair_lower_scaled (by norm_num) (by norm_num) hv0 hj hjv) hdiamond
  convert H using 1 <;> ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
