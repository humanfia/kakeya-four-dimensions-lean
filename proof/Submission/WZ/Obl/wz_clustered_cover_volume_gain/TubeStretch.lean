-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.TubeStretch.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.TubeBoxes
import Submission.WZ.Obl.wz_flat_factored_improvement.Diagonal

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox)

def tubeFrame (u : OrthonormalBasis (Fin 3) ℝ Space) (c : Space) : Space ≃ᵃⁱ[ℝ] Space :=
  u.repr.symm.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ Space c)

lemma tubeFrame_apply (u : OrthonormalBasis (Fin 3) ℝ Space) (c p : Space) :
    tubeFrame u c p = c + u.repr.symm p := rfl

lemma tubeFrame_symm_apply (u : OrthonormalBasis (Fin 3) ℝ Space) (c p : Space) :
    (tubeFrame u c).symm p = u.repr (p - c) := by
  apply (tubeFrame u c).injective
  rw [AffineIsometryEquiv.apply_symm_apply, tubeFrame_apply, u.repr.symm_apply_apply]
  abel

def transverseScales (t : ℝ) : Fin 3 → ℝ := ![1, t, t]

lemma transverseScales_pos {t : ℝ} (ht : 0 < t) : ∀ j, 0 < transverseScales t j := by
  intro j
  fin_cases j <;> simp [transverseScales, ht]

def tubeStretch (u : OrthonormalBasis (Fin 3) ℝ Space) (c : Space) (t : ℝ)
    (ht : 0 < t) : Space ≃ᵃ[ℝ] Space :=
  (coordinateAffine (tubeFrame u c) (transverseScales t)
    (fun j => (transverseScales_pos ht j).ne')).trans (tubeFrame u c).toAffineEquiv

lemma tubeStretch_apply (u : OrthonormalBasis (Fin 3) ℝ Space) (c : Space) {t : ℝ}
    (ht : 0 < t) (p : Space) :
    tubeStretch u c t ht p = c + u.repr.symm (diagonalMap (transverseScales t) (u.repr (p - c))) := by
  change tubeFrame u c (coordinateAffine (tubeFrame u c) (transverseScales t) _ p) = _
  rw [tubeFrame_apply, coordinateAffine_apply, tubeFrame_symm_apply]

lemma tubeStretch_coordinates (u : OrthonormalBasis (Fin 3) ℝ Space) (c : Space) {t : ℝ}
    (ht : 0 < t) (p : Space) (j : Fin 3) :
    inner ℝ (u j) (tubeStretch u c t ht p - c) =
      transverseScales t j * inner ℝ (u j) (p - c) := by
  rw [tubeStretch_apply, add_sub_cancel_left, ← OrthonormalBasis.repr_apply_apply,
    u.repr.apply_symm_apply, diagonalMap_apply, OrthonormalBasis.repr_apply_apply]

lemma tubeStretch_volume (u : OrthonormalBasis (Fin 3) ℝ Space) (c : Space) {t : ℝ}
    (ht : 0 < t) (A : Set Space) :
    volume (tubeStretch u c t ht '' A) = ENNReal.ofReal (t ^ 2) * volume A := by
  change volume ((fun p => tubeFrame u c
    (coordinateAffine (tubeFrame u c) (transverseScales t) _ p)) '' A) = _
  rw [← image_image, WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image,
    coordinateAffine_volume _ _ (transverseScales_pos ht)]
  congr 2
  simp [transverseScales, Fin.prod_univ_three, pow_two]

lemma tubeStretch_mem_box (u : OrthonormalBasis (Fin 3) ℝ Space) (x : Space)
    {d r : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hr : 0 < r) {p : Space}
    (hp : p ∈ Tube d x (u 0)) :
    tubeStretch u (x + (1 / 2 : ℝ) • u 0) (r / d) (div_pos hr hd) p ∈
      orthogonalBox ![2, 2 * r, 2 * r] (x + (1 / 2 : ℝ) • u 0) u := by
  intro j
  rw [tubeStretch_coordinates, abs_mul, abs_of_pos (transverseScales_pos (div_pos hr hd) j)]
  have hi := tube_midpoint_coordinates u x hp j
  fin_cases j <;> simp [transverseScales] at hi ⊢
  · linarith
  · have hh := mul_le_mul_of_nonneg_left hi (le_of_lt (div_pos hr hd))
    have he : r / d * d = r := div_mul_cancel₀ r hd.ne'
    rw [he] at hh
    linarith
  · have hh := mul_le_mul_of_nonneg_left hi (le_of_lt (div_pos hr hd))
    have he : r / d * d = r := div_mul_cancel₀ r hd.ne'
    rw [he] at hh
    linarith

lemma tubeStretch_dist_le (u : OrthonormalBasis (Fin 3) ℝ Space) (x : Space)
    {d r : ℝ} (hd : 0 < d) (hdr : d ≤ r) {p : Space} (hp : p ∈ Tube d x (u 0)) :
    dist (tubeStretch u (x + (1 / 2 : ℝ) • u 0) (r / d) (div_pos (hd.trans_le hdr) hd) p) p ≤ 2 * r := by
  let c := x + (1 / 2 : ℝ) • u 0
  let f := tubeStretch u c (r / d) (div_pos (hd.trans_le hdr) hd)
  have ht : 1 ≤ r / d := (le_div_iff₀ hd).mpr (by simpa using hdr)
  have hcoord (j : Fin 3) : |u.repr (f p - p) j| ≤ r := by
    rw [OrthonormalBasis.repr_apply_apply]
    have he : f p - p = (f p - c) - (p - c) := by abel
    rw [he, inner_sub_right, tubeStretch_coordinates]
    have hi := tube_midpoint_coordinates u x hp j
    have hid : (r / d - 1) * d ≤ r := by
      rw [sub_mul, div_mul_cancel₀ r hd.ne', one_mul]
      linarith
    fin_cases j
    · simpa [transverseScales] using (hd.trans_le hdr).le
    · dsimp [transverseScales]
      rw [← sub_one_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht)]
      exact (mul_le_mul_of_nonneg_left (by simpa [c] using hi) (sub_nonneg.mpr ht)).trans hid
    · dsimp [transverseScales]
      rw [← sub_one_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht)]
      exact (mul_le_mul_of_nonneg_left (by simpa [c] using hi) (sub_nonneg.mpr ht)).trans hid
  have hh := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
    (hd.trans_le hdr).le hcoord
  rwa [u.repr.norm_map, ← dist_eq_norm] at hh

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
