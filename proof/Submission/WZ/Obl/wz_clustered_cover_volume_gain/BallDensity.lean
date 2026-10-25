-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.BallDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.LocalToGlobal
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeBoxes

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

lemma measurable_ball_mass {U : Set Space} (hU : MeasurableSet U) (r : ℝ) :
    Measurable (fun p : Space => volume (U ∩ ball p r)) := by
  let S : Set (Space × Space) := {q | q.2 ∈ U ∧ dist q.2 q.1 < r}
  have hS : MeasurableSet S := (measurable_snd hU).inter
    (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet
  exact measurable_measure_prodMk_left hS

lemma ball_volume_lower (x : Space) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (r ^ 3) ≤ volume (ball x r) := by
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (pow_nonneg hr 3)]
  apply ENNReal.ofReal_le_ofReal
  have hpi := Real.pi_gt_three
  nlinarith [pow_nonneg hr 3]

lemma closedBall_volume_upper (x : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) ≤ ENNReal.ofReal (8 * r ^ 3) := by
  have hh := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_le_of_coords
    (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal (fun _ => x) (fun _ => r)
    (closedBall x r) (by
      intro p hp j
      have h := abs_real_inner_le_norm ((EuclideanSpace.basisFun (Fin 3) ℝ) j) (p - x)
      rw [(EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one, one_mul] at h
      exact h.trans hp)
  convert hh using 1
  congr 1
  simp [pow_succ]

/-- A lower density bound at the centres controls the measure of their
neighbourhood by the original set. -/
lemma thickening_volume_of_ball_density {U Z : Set Space} {r lam : ℝ}
    (hr : 0 < r) (hZ : Bornology.IsBounded Z) (hU : MeasurableSet U)
    (hlower : ∀ p ∈ Z, ENNReal.ofReal (lam * r ^ 3) ≤ volume (U ∩ ball p r)) :
    ENNReal.ofReal lam * volume (thickening r Z) ≤ ENNReal.ofReal 512 * volume U := by
  have hTB : TotallyBounded (thickening r Z) := (isCompact_of_isClosed_isBounded isClosed_closure hZ.thickening.closure).totallyBounded.subset subset_closure
  have hglobal := local_mass_to_global hr hTB hU
    (m := ENNReal.ofReal (512 * r ^ 3)) (q := ENNReal.ofReal (lam * r ^ 3))
    (fun x _ => (measure_mono inter_subset_right).trans
      ((closedBall_volume_upper x (show 0 ≤ 4 * r by positivity)).trans_eq (by congr 1; ring)))
    (by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := mem_thickening_iff.mp hx
      apply (hlower p hp).trans
      apply measure_mono
      intro y hy
      refine ⟨hy.1, ?_⟩
      have hh := dist_triangle y p x
      have hpy : dist y p < r := hy.2
      rw [dist_comm p x] at hh
      change dist y x < 2 * r
      linarith)
  have hr3 : 0 < ENNReal.ofReal (r ^ 3) := ENNReal.ofReal_pos.mpr (by positivity)
  apply (ENNReal.mul_le_mul_iff_right hr3.ne' ENNReal.ofReal_ne_top).mp
  convert hglobal using 1
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3)]
    congr 2
    ring
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3)]
    congr 2
    ring

/-- Upper local density on a set in a box controls its total mass by the
volume of a slightly expanded box. -/
lemma ball_density_mass_in_box {F U : Set Space} {r lam : ℝ}
    (hr : 0 < r) (hF : TotallyBounded F) (hFU : F ⊆ U)
    (w : Fin 3 → ℝ) (c : Space) (u : OrthonormalBasis (Fin 3) ℝ Space)
    (hbox : F ⊆ orthogonalBox w c u)
    (hupper : ∀ p ∈ F, volume (U ∩ ball p r) ≤ ENNReal.ofReal (lam * r ^ 3)) :
    volume F ≤ ENNReal.ofReal (64 * lam) * volume (orthogonalBox (fun j => w j + r) c u) := by
  let E := orthogonalBox (fun j => w j + r) c u
  have hglobal := local_mass_to_global (E := E) (show 0 < r / 8 by positivity) hF
    (orthogonalBox_closed _ _ _).measurableSet
    (m := ENNReal.ofReal (lam * r ^ 3)) (q := ENNReal.ofReal ((r / 4) ^ 3))
    (by
      intro x hx
      apply le_trans (measure_mono ?_) (hupper x hx)
      intro y hy
      refine ⟨hFU hy.1, ?_⟩
      have hh : dist y x ≤ 4 * (r / 8) := hy.2
      change dist y x < r
      linarith)
    (by
      intro x hx
      apply (ball_volume_lower x (show 0 ≤ r / 4 by positivity)).trans
      apply measure_mono
      intro y hy
      have hdist : ‖y - x‖ < r / 4 := hy
      refine ⟨?_, by change dist y x < 2 * (r / 8); change dist y x < r / 4 at hy; linarith⟩
      intro j
      have he : y - c = (y - x) + (x - c) := by abel
      rw [he, inner_add_right]
      have hi := abs_real_inner_le_norm (u j) (y - x)
      rw [u.norm_eq_one, one_mul] at hi
      exact (abs_add_le _ _).trans (by linarith [hbox hx j]))
  have hq : 0 < ENNReal.ofReal ((r / 4) ^ 3) := ENNReal.ofReal_pos.mpr (by positivity)
  apply (ENNReal.mul_le_mul_iff_right hq.ne' ENNReal.ofReal_ne_top).mp
  convert hglobal using 1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (r / 4) ^ 3)]
  congr 2
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
