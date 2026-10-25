-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.NormalLine.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.GraphLine

namespace WangZahlLot.Obl.wz_slab_local_linearity

open Set Metric

/-- A quarter-turn of a plane vector. -/
def perpendicular (e : Plane) : Plane := !₂[-e 1, e 0]

lemma perpendicular_ne_zero {e : Plane} (he : ‖e‖ = 1) : perpendicular e ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp [perpendicular] at h0 h1
  have hn := EuclideanSpace.real_norm_sq_eq e
  simp [he, Fin.sum_univ_two, h0, h1] at hn

lemma hyperplane_eq_line {e : Plane} (he : ‖e‖ = 1) (c : ℝ) :
    {q : Plane | inner ℝ q e = c} = range (fun t : ℝ => c • e + t • perpendicular e) := by
  have hn : (e 0) ^ 2 + (e 1) ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq e
    simpa [he, Fin.sum_univ_two] using h.symm
  ext q
  constructor
  · intro hq
    have hc : q 0 * e 0 + q 1 * e 1 = c := by
      simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hq
    refine ⟨-q 0 * e 1 + q 1 * e 0, ?_⟩
    ext i
    fin_cases i
    · simp [perpendicular, PiLp.add_apply, PiLp.smul_apply]
      linear_combination -(e 0) * hc + (q 0) * hn
    · simp [perpendicular, PiLp.add_apply, PiLp.smul_apply]
      linear_combination -(e 1) * hc + (q 1) * hn
  · rintro ⟨t, rfl⟩
    change inner ℝ (c • e + t • perpendicular e) e = c
    simp [PiLp.inner_apply, Fin.sum_univ_two, perpendicular]
    linear_combination c * hn

/-- The scalar strict strip condition is exactly enough for open line thickening. -/
lemma mem_line_thickening_of_abs_inner {q e : Plane} {c δ : ℝ}
    (he : ‖e‖ = 1) (hq : |inner ℝ q e - c| < δ) :
    q ∈ thickening δ (range (fun t : ℝ => c • e + t • perpendicular e)) := by
  rw [← hyperplane_eq_line he]
  refine mem_thickening_iff.mpr ⟨q - (inner ℝ q e - c) • e, ?_, ?_⟩
  · change inner ℝ (q - (inner ℝ q e - c) • e) e = c
    simp [inner_sub_left, real_inner_smul_left, he]
  · simpa [dist_eq_norm, norm_smul, he] using hq

end WangZahlLot.Obl.wz_slab_local_linearity
