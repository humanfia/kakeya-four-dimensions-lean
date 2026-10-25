-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.RepresentativeCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.AlignedCovers
import Submission.WZ.Obl.wz_multiscale_finite_tower.CountComparison

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (doubled centered_segment ConvexCount convexExpansionLoss tube_subset_doubled)

lemma doubled_dilation_representative {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    {x v y w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hT : Tube s x v ⊆ doubled r y w) :
    doubled r y w ⊆ AffineMap.homothety (axisMidpoint x v) (6 : ℝ) '' Tube (320 * r) x v := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := doubled_cover_representative hs hv hw hT p hp
  let q := axisMidpoint x v + (1 / 6 : ℝ) • (p - axisMidpoint x v)
  have hq : q ∈ Tube (320 * r) x v := by
    have ha' : |a / 6| ≤ 1 / 2 := by rw [abs_div]; norm_num; linarith
    refine mem_thickening_iff.mpr ⟨axisMidpoint x v + (a / 6) • v,
      centered_segment x v ha', ?_⟩
    rw [dist_eq_norm]
    have he : q - (axisMidpoint x v + (a / 6) • v) =
        (1 / 6 : ℝ) • (p - (axisMidpoint x v + a • v)) := by dsimp [q]; module
    rw [he, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith
  refine ⟨q, hq, ?_⟩
  rw [AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp [q]
  module

lemma tube_ball_of_midpoint {r : ℝ} (hr : r ≤ 1) {x v : Space}
    (hv : ‖v‖ = 1) (hmid : ‖axisMidpoint x v‖ ≤ 1) : Tube r x v ⊆ ball 0 3 := by
  intro p hp
  have hh := WangZahlLot.Obl.wz_rescaled_fibre_alternatives.tube_dist_midpoint hv hp
  change dist p (axisMidpoint x v) < r + 1 / 2 at hh
  have ht := dist_triangle p (axisMidpoint x v) 0
  simp only [dist_zero_right] at ht
  exact mem_ball_zero_iff.mpr (by linarith)

/-- Replacing each coarse axis by a child axis preserves convex counts. This
statement allows additional radius enlargement for later scale synchronization. -/
theorem representative_convex_count {s r R L : ℝ}
    (hs : 0 < s) (hr : 0 < r) (hR : 320 * r ≤ R) (hR1 : R ≤ 1) (hL : 0 ≤ L)
    {n : ℕ} (P : Fin n → Prop) (x v y w : Fin n → Space)
    (hv : ∀ i, P i → ‖v i‖ = 1) (hw : ∀ i, P i → ‖w i‖ = 1)
    (hmid : ∀ i, P i → ‖axisMidpoint (x i) (v i)‖ ≤ 1)
    (hT : ∀ i, P i → Tube s (x i) (v i) ⊆ doubled r (y i) (w i))
    (hK : ConvexCount r L P (fun i => Tube r (y i) (w i))) :
    ConvexCount R ((R / r) ^ 2 * L * convexExpansionLoss 6) P
      (fun i => Tube R (x i) (v i)) := by
  have hR0 : 0 < R := (mul_pos (by norm_num) hr).trans_le hR
  apply convex_count_of_expansions (r := r) (A := (R / r) ^ 2) (C := 6) (R := 3)
    (by positivity) (by norm_num) hL (by field_simp; rfl) P
    (fun i => Tube R (x i) (v i)) (fun i => Tube r (y i) (w i))
    (fun i => axisMidpoint (x i) (v i))
  · intro i hi
    exact isOpen_thickening
  · intro i hi
    exact tube_ball_of_midpoint hR1 (hv i hi) (hmid i hi)
  · intro i hi
    exact self_subset_thickening hR0 _ (by
      simpa only [axisMidpoint, zero_smul, add_zero] using
        centered_segment (x i) (v i) (a := 0) (by norm_num))
  · intro i hi
    exact (tube_subset_doubled hr.le (y i) (w i)).trans
      ((doubled_dilation_representative hs hr (hv i hi) (hw i hi) (hT i hi)).trans
        (image_mono (thickening_mono hR _)))
  · exact hK

end WangZahlLot.Obl.wz_multiscale_finite_tower
