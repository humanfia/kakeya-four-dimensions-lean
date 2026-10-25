-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.PrismNeighborhoods.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Geometry
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file PrismNeighborhoods.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- Thickening a prism by twice its smallest half-width costs at most a factor 27. -/
lemma thickening_twice_prism_volume_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) (c e₁ e₂ e₃ : Space) (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    volume (thickening (2 * a) (prism a b c e₁ e₂ e₃)) ≤
      27 * volume (prism a b c e₁ e₂ e₃) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have ha1 : a ≤ 1 := hab.trans hb
  calc
    _ ≤ volume (frameBox ![a + 2 * a, b + 2 * a, 1 + 2 * a] c (orthonormalFrame he)) :=
      measure_mono (thickening_prism_subset_box c e₁ e₂ e₃ he)
    _ = ENNReal.ofReal (8 * ((a + 2 * a) * (b + 2 * a) * (1 + 2 * a))) := by
      rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_orthogonalBox]
      · simp [Fin.prod_univ_three, mul_assoc]
      · intro i
        fin_cases i <;> simp <;> positivity
    _ ≤ _ := by
      rw [prism_volume ha hb0 c e₁ e₂ e₃ he, ← ENNReal.ofReal_ofNat 27,
        ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have h₂ : b + 2 * a ≤ 3 * b := by linarith
      have h₃ : 1 + 2 * a ≤ 3 := by linarith
      calc
        _ ≤ 8 * ((3 * a) * (3 * b) * 3) := by gcongr <;> linarith
        _ = _ := by ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
