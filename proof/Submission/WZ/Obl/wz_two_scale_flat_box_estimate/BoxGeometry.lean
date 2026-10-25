-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.BoxGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox
import Submission.WZ.Obl.wz_frostman_rigid_copies_volume

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (coordinateBox volume_coordinateBox)

noncomputable def boxFrame (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Space ≃ᵃⁱ[ℝ] Space :=
  e.symm.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ z)

@[simp] lemma boxFrame_apply (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) :
    boxFrame z e p = e.symm p + z := rfl

@[simp] lemma boxFrame_symm_apply (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) :
    (boxFrame z e).symm p = e (p - z) := rfl

lemma box_eq_image (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Box a b c z e = boxFrame z e '' coordinateBox ![a / 2, b / 2, c / 2] := by
  ext p
  constructor
  · intro hp
    refine ⟨e (p - z), ?_, by simp⟩
    simpa [Box, coordinateBox, Fin.forall_fin_succ] using hp
  · rintro ⟨q, hq, rfl⟩
    simp only [Box, mem_ofPred_eq, boxFrame_apply, add_sub_cancel_right, e.apply_symm_apply]
    exact ⟨hq 0, hq 1, hq 2⟩

lemma box_isClosed (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    IsClosed (Box a b c z e) := by
  exact (isClosed_le (show Continuous (fun p : Space => |e (p - z) 0|) by fun_prop)
      continuous_const).inter
    ((isClosed_le (show Continuous (fun p : Space => |e (p - z) 1|) by fun_prop)
      continuous_const).inter
      (isClosed_le (show Continuous (fun p : Space => |e (p - z) 2|) by fun_prop) continuous_const))

lemma coordinateBox_convex (w : Fin 3 → ℝ) : Convex ℝ (coordinateBox w) := by
  have he : coordinateBox w =
      (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)) ⁻¹' Set.Icc (-w) w := by
    ext p
    simp only [coordinateBox, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def, Pi.neg_apply,
      abs_le, WithLp.linearEquiv_apply]
    exact forall_and
  rw [he]
  exact (convex_Icc _ _).linear_preimage (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

lemma box_convex (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    Convex ℝ (Box a b c z e) := by
  rw [box_eq_image]
  exact (coordinateBox_convex _).affine_image (boxFrame z e).toAffineEquiv.toAffineMap

lemma box_subset_closedBall {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hc : 0 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Box a b c z e ⊆ closedBall z c := by
  intro p hp
  have hcoords : ∀ i, |e (p - z) i| ≤ c / 2 := by
    intro i
    fin_cases i
    · exact hp.1.trans (by linarith)
    · exact hp.2.1.trans (by linarith)
    · exact hp.2.2
  have hn := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
    (by positivity : 0 ≤ c / 2) hcoords
  rw [e.norm_map] at hn
  rw [mem_closedBall, dist_eq_norm]
  linarith

lemma box_compact {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hc : 0 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : IsCompact (Box a b c z e) :=
  (isCompact_closedBall z c).of_isClosed_subset (box_isClosed _ _ _ _ _)
    (box_subset_closedBall hab hbc hc z e)

lemma box_volume {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    volume (Box a b c z e) = ENNReal.ofReal (a * b * c) := by
  rw [box_eq_image, WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image,
    volume_coordinateBox]
  · congr 1
    simp [Fin.prod_univ_three]
    ring
  · intro i
    fin_cases i <;> dsimp <;> positivity

lemma homothety_box_subset_triple {a b c : ℝ} {z q : Space} {e : Space ≃ₗᵢ[ℝ] Space}
    (hq : q ∈ Box a b c z e) :
    AffineMap.homothety q (2 : ℝ) '' Box a b c z e ⊆ Box (3 * a) (3 * b) (3 * c) z e := by
  rintro _ ⟨p, hp, rfl⟩
  have he : e (AffineMap.homothety q (2 : ℝ) p - z) =
      (2 : ℝ) • e (p - z) - e (q - z) := by
    rw [← map_smul, ← map_sub]
    congr 1
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hcoord (i : Fin 3) (w : ℝ) (hpw : |e (p - z) i| ≤ w / 2)
      (hqw : |e (q - z) i| ≤ w / 2) :
      |e (AffineMap.homothety q (2 : ℝ) p - z) i| ≤ (3 * w) / 2 := by
    rw [he]
    change |2 * e (p - z) i - e (q - z) i| ≤ _
    have hh := abs_sub (2 * e (p - z) i) (e (q - z) i)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    linarith
  exact ⟨hcoord 0 a hp.1 hq.1, hcoord 1 b hp.2.1 hq.2.1, hcoord 2 c hp.2.2 hq.2.2⟩

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
