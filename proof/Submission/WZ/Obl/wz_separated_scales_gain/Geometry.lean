-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Padding

namespace WangZahlLot.Obl.wz_separated_scales_gain

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- A bounded ambient ball has a finite cover by the common grid. -/
theorem gridKey_mem_five {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {p : Space}
    (hp : p ∈ ball (0 : Space) 5) : gridKey b p ∈ gridKeys (b / 6) := by
  have hp' : (1 / 6 : ℝ) • p ∈ unitBall := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
    norm_num
    have hh := mem_ball_zero_iff.mp hp
    linarith
  have hg := gridKey_mem (by positivity : 0 < b / 6) (by linarith : b / 6 ≤ 1) hp'
  have he : gridKey (b / 6) ((1 / 6 : ℝ) • p) = gridKey b p := by
    funext i
    dsimp [gridKey]
    congr 1
    change ((1 / 6 : ℝ) * p i) / (b / 6) = p i / b
    ring
  rwa [he] at hg

theorem tube_point_dist_start {b : ℝ} {x v p : Space} (hv : ‖v‖ = 1)
    (hp : p ∈ tube b x v) : dist p x < b + 1 := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have he : dist (x + t • v) x = t := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hh := dist_triangle p (x + t • v) x
  rw [he] at hh
  linarith [ht.2]

/-- Every parent of a tube in the unit ball lies in a fixed ambient ball. -/
theorem tube_subset_ball_five {b : ℝ} (hb1 : b ≤ 1) {x v : Space}
    (hv : ‖v‖ = 1) (hmeet : (tube b x v ∩ unitBall).Nonempty) :
    tube b x v ⊆ ball (0 : Space) 5 := by
  obtain ⟨p, hpT, hpB⟩ := hmeet
  have hp := tube_point_dist_start hv hpT
  have hpn := mem_ball_zero_iff.mp hpB
  have hxn : ‖x‖ < 3 := by
    have h := norm_le_norm_add_norm_sub p x
    rw [← dist_eq_norm] at h
    linarith
  intro q hq
  have hq' := tube_point_dist_start hv hq
  rw [mem_ball_zero_iff]
  have hh := norm_le_norm_add_norm_sub x q
  rw [← dist_eq_norm, dist_comm x q] at hh
  linarith

/-- A unit tube is enclosed by an isometric image of the square model prism. -/
theorem tube_in_square_prism {b : ℝ} (hb1 : b ≤ 1) (x v : Space) (hv : ‖v‖ = 1) :
    ∃ e : AffineIsometryEquiv ℝ Space Space, tube b x v ⊆ e '' standardPrism b b := by
  obtain ⟨f, hf⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hv
  let l : Space ≃ₗᵢ[ℝ] Space := f.repr.symm
  let q : Space ≃ₗᵢ[ℝ] Space :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 2)
  let e : AffineIsometryEquiv ℝ Space Space :=
    (q.trans l).toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ Space (x + (1 / 2 : ℝ) • v))
  have hel : e.linearIsometryEquiv (EuclideanSpace.single 2 1) = v := by
    change l (q (EuclideanSpace.single 2 1)) = v
    have he : q (EuclideanSpace.single 2 1) = EuclideanSpace.single 0 1 := by
      ext i
      fin_cases i <;> simp [q, EuclideanSpace.single, Equiv.swap_apply_def]
    rw [he]
    simpa [l] using hf
  have he0 : e 0 = x + (1 / 2 : ℝ) • v := by simp [e]
  refine ⟨e, ?_⟩
  intro p hp
  refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
  obtain ⟨a, ha, hpa⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  simp only [add_sub_cancel_left] at hpa
  have hev : e ((t - 1 / 2) • EuclideanSpace.single 2 1) = x + t • v := by
    have he := e.map_vadd (0 : Space) ((t - 1 / 2) • EuclideanSpace.single 2 1)
    simp only [vadd_eq_add, add_zero, map_smul, hel, he0] at he
    rw [he]
    module
  have hd : ‖e.symm p - (t - 1 / 2) • EuclideanSpace.single 2 1‖ < b := by
    rw [← dist_eq_norm, ← e.dist_map, e.apply_symm_apply, hev]
    exact hpa
  have hcoord (i : Fin 3) :
      |(e.symm p - (t - 1 / 2) • EuclideanSpace.single 2 1 : Space) i| < b := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le _ i).trans_lt hd
  have h0 := hcoord 0
  have h1 := hcoord 1
  have h2 := hcoord 2
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply] at h0 h1 h2
  norm_num at h0 h1 h2
  refine ⟨h0.le, h1.le, ?_⟩
  rw [abs_lt] at h2
  rw [abs_le]
  constructor <;> linarith [ht.1, ht.2]

end WangZahlLot.Obl.wz_separated_scales_gain
