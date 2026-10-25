-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.TubeBoxes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.EnlargedBodies
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox
  orthogonalBox_subset_ball)
open WangZahlLot.Obl.wz_flat_factored_improvement

lemma orthogonalBox_closed (w : Fin 3 → ℝ) (c : Space)
    (u : OrthonormalBasis (Fin 3) ℝ Space) : IsClosed (orthogonalBox w c u) := by
  have he : orthogonalBox w c u = ⋂ i, {p | |inner ℝ (u i) (p - c)| ≤ w i} := by
    ext p
    simp [orthogonalBox]
  rw [he]
  exact isClosed_iInter fun i =>
    isClosed_le ((continuous_const.inner (continuous_id.sub continuous_const)).abs) continuous_const

lemma orthogonalBox_convex (w : Fin 3 → ℝ) (c : Space)
    (u : OrthonormalBasis (Fin 3) ℝ Space) : Convex ℝ (orthogonalBox w c u) := by
  have he : orthogonalBox w c u = ⋂ i, {p | |inner ℝ (u i) (p - c)| ≤ w i} := by
    ext p
    simp [orthogonalBox]
  rw [he]
  apply convex_iInter
  intro i
  have hh : Convex ℝ ((fun p : Space => inner ℝ (u i) p) ⁻¹' Icc (-w i) (w i)) :=
    (convex_Icc (-w i) (w i)).linear_preimage (innerSL ℝ (u i)).toLinearMap
  have ht := hh.translate_preimage_left (-c)
  change Convex ℝ {p : Space | -w i ≤ inner ℝ (u i) (p + -c) ∧
    inner ℝ (u i) (p + -c) ≤ w i} at ht
  simpa only [← abs_le, sub_eq_add_neg] using ht

/-- A fixed homothety of a tube box has uniform normalized body geometry. -/
lemma tube_box_geometry {n : ℕ} {r d : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hdr : d ≤ r / 4) (c : Fin n → Space) (u : Fin n → OrthonormalBasis (Fin 3) ℝ Space)
    (hc : ∀ i, ‖c i‖ ≤ 3 / 8) :
    BodyGeometry (fun i => orthogonalBox ![1 / 4, r / 4, r / 4] (c i) (u i))
      c d (r / 8) (r ^ 2 / 8) := by
  have hbound (i : Fin n) : orthogonalBox ![1 / 4, r / 4, r / 4] (c i) (u i) ⊆ ball 0 1 := by
    apply orthogonalBox_subset_ball _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    · intro j
      fin_cases j <;> simp <;> linarith
    · linarith [hc i]
  refine ⟨?_, fun i => orthogonalBox_convex _ _ _,
    fun i => (hbound i).trans ball_subset_closedBall, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (isCompact_closedBall (0 : Space) 1).of_isClosed_subset
      (orthogonalBox_closed _ _ _) ((hbound i).trans ball_subset_closedBall)
  · intro i p hp j
    have hnorm : ‖p - c i‖ < d := hp
    have hi := abs_real_inner_le_norm (u i j) (p - c i)
    rw [(u i).norm_eq_one, one_mul] at hi
    have hj : r / 4 ≤ (![1 / 4, r / 4, r / 4] : Fin 3 → ℝ) j := by
      fin_cases j <;> simp <;> linarith
    exact hi.trans ((le_of_lt hnorm).trans (hdr.trans hj))
  · intro i
    refine ⟨c i + (1 / 4 : ℝ) • u i 0, ?_, c i, ?_, ?_⟩
    · intro j
      simp only [add_sub_cancel_left, inner_smul_right, (u i).inner_eq_ite]
      fin_cases j <;> simp <;> positivity
    · intro j
      simp only [sub_self, inner_zero_right, abs_zero]
      fin_cases j <;> simp <;> positivity
    · norm_num [dist_eq_norm, norm_smul, (u i).norm_eq_one]
  · intro i
    have hw := wideSection_of_diamond (U := orthogonalBox ![1 / 4, r / 4, r / 4] (c i) (u i)) (show 0 ≤ r / 4 by positivity) (c i) (u i 1) (u i 2)
      ((u i).norm_eq_one _) ((u i).norm_eq_one _)
      (by simp [(u i).inner_eq_ite]) ?_
    · convert hw using 1 <;> ring
    · intro s t hst j
      have hs : |s| ≤ r / 4 := by linarith [abs_nonneg t]
      have ht : |t| ≤ r / 4 := by linarith [abs_nonneg s]
      have he : c i + s • u i 1 + t • u i 2 - c i = s • u i 1 + t • u i 2 := by abel
      rw [he, inner_add_right, inner_smul_right, inner_smul_right,
        (u i).inner_eq_ite, (u i).inner_eq_ite]
      fin_cases j <;> simp_all
  · intro i
    have hv : volume (orthogonalBox ![1 / 4, r / 4, r / 4] (c i) (u i)) =
        ENNReal.ofReal (r ^ 2 / 8) := by
      rw [volume_orthogonalBox]
      · congr 1
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val, Fin.isValue]
        ring
      · intro j
        fin_cases j <;> simp <;> positivity
    rw [hv]
    exact ⟨le_rfl, ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg r])⟩

/-- Coordinates of a unit tube about its midpoint. -/
lemma tube_midpoint_coordinates (u : OrthonormalBasis (Fin 3) ℝ Space) (x : Space)
    {r : ℝ} {p : Space} (hp : p ∈ Tube r x (u 0)) (j : Fin 3) :
    |inner ℝ (u j) (p - (x + (1 / 2 : ℝ) • u 0))| ≤
      if j = 0 then r + 1 / 2 else r := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left, dist_eq_norm] at hpq
  have he : p - (x + (1 / 2 : ℝ) • u 0) =
      (p - (x + t • u 0)) + (t - 1 / 2) • u 0 := by module
  rw [he, inner_add_right, inner_smul_right, u.inner_eq_ite]
  have hi := abs_real_inner_le_norm (u j) (p - (x + t • u 0))
  rw [u.norm_eq_one, one_mul] at hi
  by_cases hj : j = 0
  · simp only [hj, ite_true, mul_one] at *
    have ht' : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr (by constructor <;> linarith [ht.1, ht.2])
    exact (abs_add_le _ _).trans (by linarith)
  · simp only [hj, ite_false, mul_zero, add_zero]
    exact hi.trans hpq.le

lemma tube_subset_midpoint_box (u : OrthonormalBasis (Fin 3) ℝ Space) (x : Space)
    {r : ℝ} (hr1 : r ≤ 1) :
    Tube r x (u 0) ⊆ orthogonalBox ![2, 2 * r, 2 * r] (x + (1 / 2 : ℝ) • u 0) u := by
  intro p hp j
  have hr : 0 < r := dist_nonneg.trans_lt (mem_thickening_iff.mp hp).choose_spec.2
  have hi := tube_midpoint_coordinates u x hp j
  fin_cases j <;> simp at hi ⊢ <;> linarith

lemma tube_midpoint_norm {r : ℝ} (hr : 0 < r) (x : Space)
    (u : OrthonormalBasis (Fin 3) ℝ Space) (hT : Tube r x (u 0) ⊆ ball 0 1) :
    ‖x + (1 / 2 : ℝ) • u 0‖ ≤ 3 / 2 := by
  have hx := hT (self_subset_thickening hr _ (left_mem_segment ℝ x (x + u 0)))
  have hx' : ‖x‖ < 1 := by simpa using hx
  have h := norm_add_le x ((1 / 2 : ℝ) • u 0)
  norm_num [norm_smul, u.norm_eq_one] at h
  linarith

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
