-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PrismBodyNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PrismBodyNormalization.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalNormalization
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.VolumeWidth

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (frozenBasis frozenBasis_apply inner_boxAxis tubeFrame tubeFrame_symm_apply wideSection_of_volume)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (coordinateAffine coordinateAffine_apply diagonalMap_apply coordinateAffine_volume
    coordinateAffine_dist_lower BodyGeometry)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (norm_sq_coords)

noncomputable section

/-- Normalize a prism of fixed long dimension without losing the macroscopic
length needed by the accepted body estimate. -/
theorem fixed_prism_normalization_coordinates {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (1 / (4 * a * b)) * μ W) ∧
      f '' P a b 4 z e ⊆ ball (0 : V) 1 ∧
      (∀ p q, dist p q / 4 ≤ dist (f p) (f q)) ∧
      (∀ p i, f p i = (![a⁻¹, b⁻¹, 1 / 4] : Fin 3 → ℝ) i * e (p - z) i) := by
  have hbpos : 0 < b := ha.trans_le hab
  let s : Fin 3 → ℝ := ![a⁻¹, b⁻¹, 1 / 4]
  have hs (j : Fin 3) : 0 < s j := by fin_cases j <;> dsimp [s] <;> positivity
  let f := coordinateAffine (tubeFrame (frozenBasis e) z) s (fun j => (hs j).ne')
  have hcoord (p : V) (j : Fin 3) : f p j = s j * e (p - z) j := by
    simp only [f, coordinateAffine_apply, diagonalMap_apply, tubeFrame_symm_apply,
      OrthonormalBasis.repr_apply_apply, frozenBasis_apply, inner_boxAxis]
  have hprod : (∏ j, s j) = 1 / (4 * a * b) := by
    rw [Fin.prod_univ_three]
    change a⁻¹ * b⁻¹ * (1 / 4) = _
    ring
  refine ⟨f, ?_, ?_, ?_, hcoord⟩
  · intro W
    simpa only [hprod] using coordinateAffine_volume (tubeFrame (frozenBasis e) z) s hs W
  · rintro _ ⟨p, hp, rfl⟩
    have hi (j : Fin 3) : |f p j| ≤ 1 / 2 := by
      rw [hcoord, abs_mul, abs_of_pos (hs j)]
      fin_cases j
      · change a⁻¹ * |e (p - z) 0| ≤ 1 / 2
        apply (mul_le_mul_of_nonneg_left hp.1 (by positivity)).trans_eq
        field_simp
      · change b⁻¹ * |e (p - z) 1| ≤ 1 / 2
        apply (mul_le_mul_of_nonneg_left hp.2.1 (by positivity)).trans_eq
        field_simp
      · change (1 / 4 : ℝ) * |e (p - z) 2| ≤ 1 / 2
        linarith [hp.2.2]
    have hi2 (j : Fin 3) : (f p j) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      sq_le_sq' (abs_le.mp (hi j)).1 (abs_le.mp (hi j)).2
    rw [mem_ball_zero_iff]
    nlinarith [norm_sq_coords (f p), hi2 0, hi2 1, hi2 2, norm_nonneg (f p)]
  · intro p q
    apply (show dist p q / 4 = (1 / 4 : ℝ) * dist p q by ring).le.trans
    exact coordinateAffine_dist_lower (tubeFrame (frozenBasis e) z) (fun j => (hs j).ne')
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (fun j => by
        rw [abs_of_pos (hs j)]
        fin_cases j
        · change (1 / 4 : ℝ) ≤ a⁻¹
          rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) ha]
          linarith
        · change (1 / 4 : ℝ) ≤ b⁻¹
          rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num) hbpos]
          linarith
        · exact le_rfl) p q

theorem fixed_prism_normalization {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (1 / (4 * a * b)) * μ W) ∧
      f '' P a b 4 z e ⊆ ball (0 : V) 1 ∧
      (∀ p q, dist p q / 4 ≤ dist (f p) (f q)) := by
  obtain ⟨f, hv, hb, hd, -⟩ := fixed_prism_normalization_coordinates ha hab hb z e
  exact ⟨f, hv, hb, hd⟩

/-- A family of long convex bodies in a common prism has a common
normalization; the exact volume supplies a lower middle width. -/
theorem prism_body_normalization {a b r d w : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (hr : 0 < r) (hd : d ≤ r / 4)
    (hw : 0 < w) {n : ℕ} (U : Fin n → Set V) (x : Fin n → V)
    (hcompact : ∀ i, IsCompact (U i)) (hconvex : ∀ i, Convex ℝ (U i))
    (hball : ∀ i, ball (x i) r ⊆ U i)
    (hlong : ∀ i, ∃ p ∈ U i, ∃ q ∈ U i, (1 / 4 : ℝ) ≤ dist p q)
    (hvolume : ∀ i, μ (U i) = O w)
    (z : V) (e : V ≃ₗᵢ[ℝ] V) (hbox : ∀ i, U i ⊆ P a b 4 z e) :
    ∃ f : V ≃ᵃ[ℝ] V,
      (∀ W, μ (f '' W) = O (1 / (4 * a * b)) * μ W) ∧
      (∀ i, f '' U i ⊆ ball (0 : V) 1) ∧
      BodyGeometry (fun i => f '' U i) (fun i => f (x i)) d
        (Real.sqrt (w / (4 * a * b)) / 16) (w / (4 * a * b)) := by
  obtain ⟨f, hvol, hunit, hdist⟩ := fixed_prism_normalization ha hab hb z e
  have hbpos : 0 < b := ha.trans_le hab
  have hbound i : f '' U i ⊆ ball (0 : V) 1 := (image_mono (hbox i)).trans hunit
  have hint i : ball (f (x i)) (r / 4) ⊆ f '' U i := by
    intro p hp
    refine ⟨f.symm p, hball i ?_, f.apply_symm_apply p⟩
    have hh := hdist (f.symm p) (x i)
    rw [f.apply_symm_apply] at hh
    rw [mem_ball] at hp ⊢
    linarith
  have hcompact' i : IsCompact (f '' U i) :=
    (hcompact i).image f.toContinuousAffineEquiv.continuous
  have hconvex' i : Convex ℝ (f '' U i) := (hconvex i).affine_image f.toAffineMap
  have hvol' i : μ (f '' U i) = O (w / (4 * a * b)) := by
    rw [hvol, hvolume, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (4 * a * b))]
    congr 1
    ring
  refine ⟨f, hvol, hbound, hcompact', hconvex', fun i => (hbound i).trans ball_subset_closedBall,
    fun i => (ball_subset_ball hd).trans (hint i), ?_, ?_, ?_⟩
  · intro i
    obtain ⟨p, hp, q, hq, hpq⟩ := hlong i
    refine ⟨f p, mem_image_of_mem f hp, f q, mem_image_of_mem f hq, ?_⟩
    linarith [hdist p q]
  · intro i
    exact wideSection_of_volume (hcompact' i) (hconvex' i) (by positivity : 0 < r / 4)
      (hint i) ((hbound i).trans ball_subset_closedBall) (by positivity) (hvol' i).ge
  · intro i
    change O (w / (4 * a * b)) ≤ μ (f '' U i) ∧
      μ (f '' U i) ≤ O (384 * (w / (4 * a * b)))
    rw [hvol' i]
    exact ⟨le_rfl, ENNReal.ofReal_le_ofReal (by nlinarith [div_pos hw (by positivity : 0 < 4 * a * b)])⟩

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
