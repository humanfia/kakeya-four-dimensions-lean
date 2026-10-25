-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Basic
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox
import Submission.WZ.Obl.wz_transverse_cell_weighted_cover.Basic
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Geometry.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

abbrev frameBox := WangZahlLot.Obl.wz_regular_transverse_affine_cells.orthogonalBox
noncomputable abbrev orthonormalFrame {u : Fin 3 → Space} (hu : Orthonormal ℝ u) :=
  WangZahlLot.Obl.wz_transverse_cell_weighted_cover.onb hu

lemma prism_eq_box (a b : ℝ) (c e₁ e₂ e₃ : Space)
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    prism a b c e₁ e₂ e₃ = frameBox ![a, b, 1] c (orthonormalFrame he) := by
  ext y
  simp only [prism, frameBox,
    WangZahlLot.Obl.wz_regular_transverse_affine_cells.orthogonalBox,
    Set.mem_setOf_eq, orthonormalFrame, WangZahlLot.Obl.wz_transverse_cell_weighted_cover.onb_apply]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩ i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₃
  · intro h
    exact ⟨h 0, h 1, h 2⟩

lemma prism_volume {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c e₁ e₂ e₃ : Space)
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    volume (prism a b c e₁ e₂ e₃) = ENNReal.ofReal (8 * a * b) := by
  rw [prism_eq_box a b c e₁ e₂ e₃ he]
  rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_orthogonalBox]
  · congr 1
    simp [Fin.prod_univ_three, mul_assoc]
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · norm_num

lemma prism_convex (a b : ℝ) (c e₁ e₂ e₃ : Space) :
    Convex ℝ (prism a b c e₁ e₂ e₃) := by
  have hs (e : Space) (t : ℝ) : Convex ℝ {y | |inner ℝ e (y - c)| ≤ t} := by
    have heq : {y | |inner ℝ e (y - c)| ≤ t} =
        (fun y => inner ℝ e y) ⁻¹' Icc (inner ℝ e c - t) (inner ℝ e c + t) := by
      ext y
      simp only [Set.mem_setOf_eq, mem_preimage, mem_Icc, inner_sub_right, abs_le]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    rw [heq]
    exact (convex_Icc _ _).linear_preimage (innerₛₗ ℝ e)
  exact (hs e₁ a).inter ((hs e₂ b).inter (hs e₃ 1))

lemma prism_isClosed (a b : ℝ) (c e₁ e₂ e₃ : Space) :
    IsClosed (prism a b c e₁ e₂ e₃) := by
  have hs (e : Space) (t : ℝ) : IsClosed {y | |inner ℝ e (y - c)| ≤ t} :=
    isClosed_le (by fun_prop) continuous_const
  exact (hs e₁ a).inter ((hs e₂ b).inter (hs e₃ 1))

lemma thickening_prism_subset_box {a b r : ℝ} (c e₁ e₂ e₃ : Space)
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    thickening r (prism a b c e₁ e₂ e₃) ⊆
      frameBox ![a + r, b + r, 1 + r] c (orthonormalFrame he) := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  rw [prism_eq_box a b c e₁ e₂ e₃ he] at hz
  intro i
  have hid : inner ℝ (orthonormalFrame he i) (y - c) =
      inner ℝ (orthonormalFrame he i) (y - z) + inner ℝ (orthonormalFrame he i) (z - c) := by
    rw [← inner_add_right]
    congr 1
    abel
  have hn : ‖orthonormalFrame he i‖ = 1 := (orthonormalFrame he).orthonormal.norm_eq_one i
  have hi : |inner ℝ (orthonormalFrame he i) (y - z)| ≤ ‖y - z‖ := by
    simpa only [hn, one_mul] using abs_real_inner_le_norm (orthonormalFrame he i) (y - z)
  have hr : ‖y - z‖ < r := by simpa only [dist_eq_norm] using hyz
  have hadd : (![a, b, 1] : Fin 3 → ℝ) i + r =
      (![a + r, b + r, 1 + r] : Fin 3 → ℝ) i := by fin_cases i <;> rfl
  calc
    |inner ℝ (orthonormalFrame he i) (y - c)| ≤
        |inner ℝ (orthonormalFrame he i) (y - z)| + |inner ℝ (orthonormalFrame he i) (z - c)| := by
      rw [hid]
      exact abs_add_le _ _
    _ ≤ (![a, b, 1] : Fin 3 → ℝ) i + r := by linarith [hz i]
    _ = _ := hadd

lemma thickening_prism_volume_le {a b r : ℝ} (ha : 0 ≤ a) (har : a ≤ r)
    (hrb : r ≤ b) (hb : b ≤ 1) (c e₁ e₂ e₃ : Space)
    (he : Orthonormal ℝ ![e₁, e₂, e₃]) :
    volume (thickening r (prism a b c e₁ e₂ e₃)) ≤ ENNReal.ofReal (64 * r * b) := by
  have hr : 0 ≤ r := ha.trans har
  have hb0 : 0 ≤ b := hr.trans hrb
  calc
    _ ≤ volume (frameBox ![a + r, b + r, 1 + r] c (orthonormalFrame he)) :=
      measure_mono (thickening_prism_subset_box c e₁ e₂ e₃ he)
    _ = ENNReal.ofReal (8 * ((a + r) * (b + r) * (1 + r))) := by
      rw [WangZahlLot.Obl.wz_regular_transverse_affine_cells.volume_orthogonalBox]
      · simp [Fin.prod_univ_three, mul_assoc]
      · intro i
        fin_cases i <;> simp <;> positivity
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h₁ : a + r ≤ 2 * r := by linarith
      have h₂ : b + r ≤ 2 * b := by linarith
      have h₃ : 1 + r ≤ 2 := by linarith
      calc
        _ ≤ 8 * ((2 * r) * (2 * b) * 2) := by gcongr
        _ = _ := by ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
