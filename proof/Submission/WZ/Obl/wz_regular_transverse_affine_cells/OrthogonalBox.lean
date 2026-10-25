-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.OrthogonalBox.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.PrincipalAxes
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ConvexFrame
import Submission.WZ.Obl.wz_balanced_cluster_cover.Basic

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module MeasureTheory Set
open scoped ENNReal

/-- A box with arbitrary three half-widths in orthonormal coordinates. -/
def orthogonalBox (w : Fin 3 → ℝ) (c : E) (u : OrthonormalBasis (Fin 3) ℝ E) : Set E :=
  {p | ∀ i, |inner ℝ (u i) (p - c)| ≤ w i}

def coordinateBox (w : Fin 3 → ℝ) : Set E := {q | ∀ i, |q i| ≤ w i}

lemma coordinateBox_measurable (w : Fin 3 → ℝ) : MeasurableSet (coordinateBox w) := by
  have he : coordinateBox w = ⋂ i, {q : E | |q i| ≤ w i} := by
    ext q; simp [coordinateBox]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply IsClosed.measurableSet
  apply isClosed_le _ continuous_const
  fun_prop

lemma volume_coordinateBox (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    volume (coordinateBox w) = ENNReal.ofReal (8 * ∏ i, w i) := by
  have he : coordinateBox w = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' Set.Icc (-w) w := by
    ext q
    simp only [coordinateBox, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def, Pi.neg_apply, abs_le]
    exact forall_and
  rw [he, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  simp only [Pi.neg_apply, sub_neg_eq_add, ← two_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by norm_num) (hw i)),
    Finset.prod_mul_distrib]
  norm_num

lemma volume_orthogonalBox (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (c : E)
    (u : OrthonormalBasis (Fin 3) ℝ E) :
    volume (orthogonalBox w c u) = ENNReal.ofReal (8 * ∏ i, w i) := by
  have he : orthogonalBox w c u = (fun p : E => p + -c) ⁻¹'
      ((u.repr : E → E) ⁻¹' coordinateBox w) := by
    ext p
    simp only [orthogonalBox, coordinateBox, mem_ofPred_eq, mem_preimage, sub_eq_add_neg,
      OrthonormalBasis.repr_apply_apply]
  rw [he, measure_preimage_add_right,
    u.measurePreserving_repr.measure_preimage (coordinateBox_measurable w).nullMeasurableSet,
    volume_coordinateBox w hw]

lemma image_ball_subset_orthogonalBox (A : E ≃ₗ[ℝ] E) (c : E)
    (u : OrthonormalBasis (Fin 3) ℝ E) (d : Fin 3 → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hcoord : ∀ q i, |inner ℝ (u i) (A q)| ≤ d i * ‖q‖)
    (R : ℝ) : (fun q => A q + c) '' Metric.closedBall 0 R ⊆
      orthogonalBox (fun i => R * d i) c u := by
  rintro p ⟨q, hq, rfl⟩ i
  rw [add_sub_cancel_right]
  have hq' : ‖q‖ ≤ R := by simpa using hq
  exact (hcoord q i).trans (by nlinarith [mul_le_mul_of_nonneg_left hq' (hd i)])

lemma orthogonalBox_subset_ball (w : Fin 3 → ℝ) (c : E)
    (u : OrthonormalBasis (Fin 3) ℝ E) {t R : ℝ} (ht : 0 ≤ t)
    (hw : ∀ i, w i ≤ t) (hR : ‖c‖ + 2 * t < R) :
    orthogonalBox w c u ⊆ Metric.ball 0 R := by
  intro p hp
  have hcoords : ∀ i, |u.repr (p - c) i| ≤ t := by
    intro i
    rw [OrthonormalBasis.repr_apply_apply]
    exact (hp i).trans (hw i)
  have hnorm := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le ht hcoords
  rw [u.repr.norm_map] at hnorm
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖p‖ ≤ ‖p - c‖ + ‖c‖ := by simpa only [add_comm] using norm_le_insert' p c
    _ < R := by linarith

lemma volume_quarter_cube : volume {q : E | ∀ i, 0 ≤ q i ∧ q i ≤ 1 / 4} =
    ENNReal.ofReal (1 / 64 : ℝ) := by
  have he : {q : E | ∀ i, 0 ≤ q i ∧ q i ≤ 1 / 4} =
      (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹' Set.Icc 0 (fun _ => 1 / 4) := by
    ext q
    simp only [mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply]
    exact forall_and
  rw [he, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi]
  norm_num [Fin.prod_univ_three, ← ENNReal.ofReal_mul]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  norm_num

lemma prism_eq_orthogonalBox (a b : ℝ) (c : E) (u : OrthonormalBasis (Fin 3) ℝ E) :
    prism a b c u = orthogonalBox ![a, b, 1 / 1000] c u := by
  ext p
  constructor
  · intro hp i
    fin_cases i
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  · intro hp
    exact ⟨hp 0, hp 1, hp 2⟩

lemma volume_prism (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (c : E)
    (u : OrthonormalBasis (Fin 3) ℝ E) :
    volume (prism a b c u) = ENNReal.ofReal (8 * a * b / 1000) := by
  rw [prism_eq_orthogonalBox, volume_orthogonalBox]
  · congr 1
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue]
    ring
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · norm_num

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
