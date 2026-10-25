-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.CoarseBodies.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.PrismNeighborhood
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyTransport

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric

noncomputable section

def coarseMap : Space ≃ᵃ[ℝ] Space :=
  (LinearEquiv.smulOfNeZero ℝ Space (1 / 32) (by norm_num)).toAffineEquiv

@[simp] theorem coarseMap_apply (p : Space) : coarseMap p = (1 / 32 : ℝ) • p := rfl

theorem coarseMap_dist (p q : Space) : dist (coarseMap p) (coarseMap q) = dist p q / 32 := by
  simp [coarseMap_apply, dist_smul₀]
  ring

theorem coarseMap_volume (Q : Set Space) :
    volume (coarseMap '' Q) = ENNReal.ofReal (1 / 32768) * volume Q := by
  change volume ((fun p : Space => (1 / 32 : ℝ) • p) '' Q) = _
  rw [WangZahlLot.Obl.wz_nonflat_factored_improvement.volume_smul_image (by norm_num : (0 : ℝ) ≤ 1 / 32)]
  norm_num

theorem WideSection.affine_image {U : Set Space} {b L : ℝ}
    (h : WideSection U b) (f : Space ≃ᵃ[ℝ] Space) (hL : 0 < L)
    (hLip : ∀ p q, dist (f.symm p) (f.symm q) ≤ L * dist p q) :
    WideSection (f '' U) (b / L) := by
  have hh := h.preimage f.symm hL hLip
  have he : f.symm ⁻¹' U = f '' U := by
    ext p
    exact ⟨fun hp => ⟨f.symm p, hp, f.apply_symm_apply p⟩,
      by rintro ⟨p, hp, rfl⟩; simpa using hp⟩
  simpa only [he] using hh

theorem standardPrism_subset_dilated {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    StandardPrism a b ⊆ dilatedPrism r a b := by
  intro p hp
  exact ⟨hp.1.trans (by nlinarith), hp.2.1.trans (by nlinarith), hp.2.2.trans (by linarith)⟩

theorem prism_center_bound {a b : ℝ} (hab : a ≤ b) (hb2 : b ≤ 2)
    (e : AffineIsometryEquiv ℝ Space Space)
    (hmeet : (e '' StandardPrism a b ∩ ball (0 : Space) 1).Nonempty) : ‖e 0‖ ≤ 5 := by
  obtain ⟨_, ⟨p, hp, rfl⟩, hB⟩ := hmeet
  have hp' : p ∈ dilatedPrism 1 a b := by simpa [dilatedPrism] using hp
  have hn : ‖p‖ ≤ 4 := by simpa using dilatedPrism_norm (by norm_num) hab hb2 hp'
  have hd : dist (e 0) (e p) ≤ 4 := by simpa using hn
  have he : ‖e p‖ < 1 := mem_ball_zero_iff.mp hB
  have hh := dist_triangle (e 0) (e p) 0
  simp only [dist_zero_right] at hh
  linarith

def coarsePrism (e : AffineIsometryEquiv ℝ Space Space) (a b : ℝ) : Set Space :=
  coarseMap '' (e '' dilatedPrism 3 a b)

theorem coarsePrism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e : AffineIsometryEquiv ℝ Space Space) :
    volume (coarsePrism e a b) = ENNReal.ofReal ((1 / 32768 : ℝ) * (432 * a * b)) := by
  rw [coarsePrism, coarseMap_volume,
    WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image,
    dilatedPrism_volume (by norm_num) ha hb, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem coarse_body_geometry {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb2 : b ≤ 2)
    (hd : d ≤ a / 32) {q : ℕ} (e : Fin q → AffineIsometryEquiv ℝ Space Space)
    (hmeet : ∀ j, (e j '' StandardPrism a b ∩ ball (0 : Space) 1).Nonempty) :
    BodyGeometry (fun j => coarsePrism (e j) a b) (fun j => coarseMap (e j 0)) d
      (b / 64) ((1 / 32768 : ℝ) * (432 * a * b)) := by
  have hb : 0 < b := ha.trans_le hab
  have hinc : StandardPrism a b ⊆ dilatedPrism 3 a b := standardPrism_subset_dilated ha.le hb.le (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ((dilatedPrism_compact (by norm_num : (0 : ℝ) ≤ 3) hab hb2).image (e j).continuous).image
      coarseMap.toContinuousAffineEquiv.continuous
  · intro j
    exact ((dilatedPrism_convex (by norm_num : (0 : ℝ) < 3) a b).affine_image
      (e j).toAffineEquiv.toAffineMap).affine_image coarseMap.toAffineMap
  · rintro j _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    have hn : ‖p‖ ≤ 12 := by
      convert dilatedPrism_norm (by norm_num : (0 : ℝ) ≤ 3) hab hb2 hp using 1 <;> norm_num
    have hc := prism_center_bound hab hb2 (e j) (hmeet j)
    have hd : dist (e j p) (e j 0) = ‖p‖ := by simp
    have hh := dist_triangle (e j p) (e j 0) 0
    rw [hd, dist_zero_right, dist_zero_right] at hh
    apply mem_closedBall_zero_iff.mpr
    simp only [coarseMap_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 32)]
    linarith
  · intro j p hp
    let z := (e j).symm (coarseMap.symm p)
    have hdist : dist (coarseMap.symm p) (e j 0) < a := by
      have hh := coarseMap_dist (coarseMap.symm p) (e j 0)
      rw [coarseMap.apply_symm_apply] at hh
      have hd' := (mem_ball.mp hp).trans_le hd
      rw [hh] at hd'
      linarith
    have hz : ‖z‖ < a := by
      have hh : dist (coarseMap.symm p) (e j 0) = ‖z‖ := by
        dsimp [z]
        rw [← (e j).symm.dist_map, (e j).symm_apply_apply, dist_zero_right]
      rwa [hh] at hdist
    have hzP : z ∈ StandardPrism a b := by
      have hi (i : Fin 3) : |z i| ≤ a := by
        have hh : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
        exact hh.trans hz.le
      exact ⟨hi 0, (hi 1).trans hab, (hi 2).trans (hab.trans hb2)⟩
    refine ⟨coarseMap.symm p, ⟨z, hinc hzP, ?_⟩, coarseMap.apply_symm_apply p⟩
    exact (e j).apply_symm_apply _
  · intro j
    let v : Space := (2 : ℝ) • EuclideanSpace.basisFun (Fin 3) ℝ 2
    have h0 : (0 : Space) ∈ StandardPrism a b := by simp [StandardPrism, ha.le, hb.le]
    have hv : v ∈ StandardPrism a b := by simp [v, StandardPrism, EuclideanSpace.basisFun_apply, ha.le, hb.le]
    refine ⟨coarseMap (e j 0), ⟨_, ⟨0, hinc h0, rfl⟩, rfl⟩,
      coarseMap (e j v), ⟨_, ⟨v, hinc hv, rfl⟩, rfl⟩, ?_⟩
    rw [coarseMap_dist, (e j).dist_map]
    rw [dist_zero_left]
    dsimp [v]
    rw [norm_smul, OrthonormalBasis.norm_eq_one]
    norm_num
  · intro j
    have hW : WideSection (e j '' StandardPrism a b) (b / 2) := by
      have hh := (standardPrism_wideSection ha.le hb.le hb2).affine_image
        (e j).toAffineEquiv (by norm_num : (0 : ℝ) < 1) (fun p q => by simp)
      simpa using hh
    have hh := (hW.mono (image_mono hinc)).affine_image coarseMap (by norm_num : (0 : ℝ) < 32)
      (fun p q => by
        have hh := coarseMap_dist (coarseMap.symm p) (coarseMap.symm q)
        rw [coarseMap.apply_symm_apply, coarseMap.apply_symm_apply] at hh
        linarith)
    change WideSection (coarseMap '' (e j '' dilatedPrism 3 a b)) (b / 64)
    convert hh using 1 <;> ring
  · intro j
    rw [coarsePrism_volume ha.le hb.le]
    refine ⟨le_rfl, ENNReal.ofReal_le_ofReal ?_⟩
    have hh : 0 ≤ (1 / 32768 : ℝ) * (432 * a * b) := by positivity
    nlinarith

end
end WangZahlLot.Obl.wz_flat_factored_improvement
