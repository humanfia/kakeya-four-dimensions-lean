-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.CoarseBoxGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_flat_factored_improvement.CoarseBodies

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (StandardPrism WideSection BodyGeometry standardPrism_wideSection)

noncomputable def boxContraction : Space ≃ᵃ[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space (1 / 64) (by norm_num)).toAffineEquiv

@[simp] lemma boxContraction_apply (p : Space) : boxContraction p = (1 / 64 : ℝ) • p := rfl

lemma boxContraction_dist (p q : Space) : dist (boxContraction p) (boxContraction q) = dist p q / 64 := by
  simp [boxContraction_apply, dist_smul₀]
  ring

lemma boxContraction_volume (W : Set Space) :
    volume (boxContraction '' W) = ENNReal.ofReal (1 / 262144) * volume W := by
  change volume ((fun p : Space => (1 / 64 : ℝ) • p) '' W) = _
  rw [WangZahlLot.Obl.wz_nonflat_factored_improvement.volume_smul_image (by norm_num : (0 : ℝ) ≤ 1 / 64)]
  norm_num

noncomputable def coarseBox (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  boxContraction '' Box (6 * a) (6 * b) (6 * c) z e

lemma box_subset_sixfold {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Box a b c z e ⊆ Box (6 * a) (6 * b) (6 * c) z e := by
  intro p hp
  exact ⟨hp.1.trans (by linarith), hp.2.1.trans (by linarith), hp.2.2.trans (by linarith)⟩

lemma box_center_norm {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hc : 0 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space)
    (hmeet : (Box a b c z e ∩ ball (0 : Space) 1).Nonempty) : ‖z‖ ≤ c + 1 := by
  obtain ⟨p, hp, hpB⟩ := hmeet
  have hd := mem_closedBall.mp (box_subset_closedBall hab hbc hc z e hp)
  have hn := mem_ball_zero_iff.mp hpB
  have hh := dist_triangle z p 0
  rw [dist_comm z p, dist_zero_right, dist_zero_right] at hh
  linarith

lemma coarseBox_volume {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    volume (coarseBox a b c z e) = ENNReal.ofReal ((1 / 262144 : ℝ) * (216 * (a * b * c))) := by
  rw [coarseBox, boxContraction_volume, box_volume (by positivity) (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 262144)]
  congr 1
  ring

lemma standardPrism_subset_sixfold_box {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 1 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    boxFrame z e '' StandardPrism a (b / 4) ⊆ Box (6 * a) (6 * b) (6 * c) z e := by
  rintro _ ⟨p, hp, rfl⟩
  change |e (e.symm p + z - z) 0| ≤ 6 * a / 2 ∧
    |e (e.symm p + z - z) 1| ≤ 6 * b / 2 ∧ |e (e.symm p + z - z) 2| ≤ 6 * c / 2
  rw [add_sub_cancel_right, e.apply_symm_apply]
  exact ⟨hp.1.trans (by linarith), hp.2.1.trans (by linarith), hp.2.2.trans (by linarith)⟩

set_option maxHeartbeats 400000 in
lemma coarse_box_geometry {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : 1 ≤ c) (hc8 : c ≤ 8) (hd : d ≤ a / 64)
    {q : ℕ} (z : Fin q → Space) (e : Fin q → Space ≃ₗᵢ[ℝ] Space)
    (hmeet : ∀ j, (Box a b c (z j) (e j) ∩ ball (0 : Space) 1).Nonempty) :
    BodyGeometry (fun j => coarseBox a b c (z j) (e j)) (fun j => boxContraction (z j)) d
      (b / 512) ((1 / 262144 : ℝ) * (216 * (a * b * c))) := by
  have hb : 0 < b := ha.trans_le hab
  have hcpos : 0 < c := zero_lt_one.trans_le hc
  have hscaledab : 6 * a ≤ 6 * b := by linarith
  have hscaledbc : 6 * b ≤ 6 * c := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (box_compact hscaledab hscaledbc (by positivity) (z j) (e j)).image
      boxContraction.toContinuousAffineEquiv.continuous
  · intro j
    exact (box_convex _ _ _ _ _).affine_image boxContraction.toAffineMap
  · rintro j _ ⟨p, hp, rfl⟩
    have hdist := mem_closedBall.mp (box_subset_closedBall hscaledab hscaledbc
      (by positivity) (z j) (e j) hp)
    have hcenter := box_center_norm hab hbc hcpos.le (z j) (e j) (hmeet j)
    have hh := dist_triangle p (z j) 0
    simp only [dist_zero_right] at hh
    apply mem_closedBall_zero_iff.mpr
    simp only [boxContraction_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 64)]
    linarith
  · intro j p hp
    let r := boxContraction.symm p
    have hr : dist r (z j) < a := by
      have hh := boxContraction_dist r (z j)
      rw [boxContraction.apply_symm_apply] at hh
      have hp' := (mem_ball.mp hp).trans_le hd
      rw [hh] at hp'
      linarith
    have hcoord (i : Fin 3) : |e j (r - z j) i| ≤ a := by
      have hh : |e j (r - z j) i| ≤ ‖e j (r - z j)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e j (r - z j)) i
      rw [(e j).norm_map] at hh
      exact hh.trans (by simpa only [dist_eq_norm] using hr.le)
    refine ⟨r, ?_, boxContraction.apply_symm_apply p⟩
    exact ⟨(hcoord 0).trans (by linarith), (hcoord 1).trans (by linarith),
      (hcoord 2).trans (by linarith)⟩
  · intro j
    let p : Space := (-2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 2
    let r : Space := (2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 2
    have hp : p ∈ StandardPrism a (b / 4) := by
      simp [p, StandardPrism, EuclideanSpace.basisFun_apply, ha.le,
        (by positivity : 0 ≤ b / 4)]
    have hr : r ∈ StandardPrism a (b / 4) := by
      simp [r, StandardPrism, EuclideanSpace.basisFun_apply, ha.le,
        (by positivity : 0 ≤ b / 4)]
    have hinc := standardPrism_subset_sixfold_box ha.le hb.le hc (z j) (e j)
    refine ⟨boxContraction (boxFrame (z j) (e j) p), ⟨_, hinc ⟨p, hp, rfl⟩, rfl⟩,
      boxContraction (boxFrame (z j) (e j) r), ⟨_, hinc ⟨r, hr, rfl⟩, rfl⟩, ?_⟩
    rw [boxContraction_dist, (boxFrame (z j) (e j)).dist_map, dist_eq_norm]
    have he : p - r = (-4 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 2 := by dsimp [p, r]; module
    rw [he, norm_smul, OrthonormalBasis.norm_eq_one]
    norm_num
  · intro j
    have hW : WideSection (boxFrame (z j) (e j) '' StandardPrism a (b / 4)) (b / 8) := by
      have hh := (standardPrism_wideSection ha.le (by positivity : 0 ≤ b / 4)
        (by linarith : b / 4 ≤ 2)).affine_image (boxFrame (z j) (e j)).toAffineEquiv
          (by norm_num : (0 : ℝ) < 1) (fun p r => by simp)
      convert hh using 1 <;> ring
    have hh := (hW.mono (standardPrism_subset_sixfold_box ha.le hb.le hc (z j) (e j))).affine_image
      boxContraction (by norm_num : (0 : ℝ) < 64) (fun p r => by
        have hh := boxContraction_dist (boxContraction.symm p) (boxContraction.symm r)
        rw [boxContraction.apply_symm_apply, boxContraction.apply_symm_apply] at hh
        linarith)
    change WideSection (boxContraction '' Box (6 * a) (6 * b) (6 * c) (z j) (e j)) (b / 512)
    convert hh using 1 <;> ring
  · intro j
    rw [coarseBox_volume ha.le hb.le hcpos.le]
    refine ⟨le_rfl, ENNReal.ofReal_le_ofReal ?_⟩
    have hh : 0 ≤ (1 / 262144 : ℝ) * (216 * (a * b * c)) := by positivity
    nlinarith

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
