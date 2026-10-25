-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264.Thickening.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_quadratic_flat_gain.X264.Geometry
-- Copied from session x0264 (o072 branch, commit c1a4bfb, file Thickening.lean), namespace renamed.

namespace WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264

open MeasureTheory Set Metric

/-- Restricted convolution converts a lower ball density in the container and an upper
ball density in a shading into a lower bound for its thickening inside the container. -/
lemma thickening_volume_mul {P Y : Set Space} (hP : MeasurableSet P) (hY : MeasurableSet Y)
    (r : ℝ) (A B : ENNReal)
    (hlo : ∀ y ∈ Y, A ≤ volume (P ∩ ball y r))
    (hhi : ∀ p : Space, volume (Y ∩ ball p r) ≤ B) :
    A * volume Y ≤ B * volume (P ∩ thickening r Y) := by
  let S : Set (Space × Space) := {q | q.1 ∈ P ∧ q.2 ∈ Y ∧ dist q.2 q.1 < r}
  have hS : MeasurableSet S := (measurable_fst hP).inter
    ((measurable_snd hY).inter
      (isOpen_lt (continuous_snd.dist continuous_fst) continuous_const).measurableSet)
  have h₁ : (volume.prod volume) S =
      ∫⁻ p : Space, P.indicator (fun p => volume (Y ∩ ball p r)) p := by
    rw [Measure.prod_apply hS]
    congr 1
    funext p
    by_cases hp : p ∈ P
    · rw [indicator_of_mem hp]
      congr 1
      ext y
      simp [S, hp]
    · rw [indicator_of_notMem hp]
      have hempty : (fun y => (p, y)) ⁻¹' S = ∅ := by ext y; simp [S, hp]
      rw [hempty, measure_empty]
  have h₂ : (volume.prod volume) S =
      ∫⁻ y : Space, Y.indicator (fun y => volume (P ∩ ball y r)) y := by
    rw [Measure.prod_apply_symm hS]
    congr 1
    funext y
    by_cases hy : y ∈ Y
    · rw [indicator_of_mem hy]
      congr 1
      ext p
      simp [S, hy, dist_comm]
    · rw [indicator_of_notMem hy]
      have hempty : (fun p => (p, y)) ⁻¹' S = ∅ := by ext p; simp [S, hy]
      rw [hempty, measure_empty]
  have hE : MeasurableSet (P ∩ thickening r Y) := hP.inter isOpen_thickening.measurableSet
  calc
    A * volume Y = ∫⁻ y : Space, Y.indicator (fun _ => A) y :=
      (lintegral_indicator_const hY A).symm
    _ ≤ (volume.prod volume) S := by
      rw [h₂]
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ Y
      · simpa only [indicator_of_mem hy] using hlo y hy
      · simp only [indicator_of_notMem hy, le_refl]
    _ ≤ ∫⁻ p : Space, (P ∩ thickening r Y).indicator (fun _ => B) p := by
      rw [h₁]
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ P
      · rw [indicator_of_mem hp]
        by_cases hpY : p ∈ thickening r Y
        · simpa only [indicator_of_mem (show p ∈ P ∩ thickening r Y from ⟨hp, hpY⟩)]
            using hhi p
        · have hempty : Y ∩ ball p r = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro y ⟨hy, hyp⟩
            exact hpY (mem_thickening_iff.mpr ⟨y, hy, by simpa only [mem_ball, dist_comm] using hyp⟩)
          simp only [hempty, measure_empty, zero_le]
      · simp only [indicator_of_notMem hp, zero_le]
    _ = B * volume (P ∩ thickening r Y) := lintegral_indicator_const hE B

/-- A tube has at most `8 r delta^2` volume in any ball of radius r. -/
lemma tube_ball_volume_le {δ r : ℝ} (x v p : Space) (hv : ‖v‖ = 1) :
    volume (tube δ x v ∩ ball p r) ≤ ENNReal.ofReal (8 * r * δ ^ 2) := by
  obtain ⟨u, hu⟩ := WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hv
  have hperp (k : Fin 3) (hk : k ≠ 0) : inner ℝ (u k) v = 0 := by
    rw [← hu, orthonormal_iff_ite.mp u.orthonormal]
    simp [hk]
  have hc (k : Fin 3) (hk : k ≠ 0) (q : Space) (hq : q ∈ tube δ x v) :
      |inner ℝ (u k) (q - x)| ≤ δ := by
    simpa only [mem_setOf_eq, inner_sub_right] using
      WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.tube_subset_slab
        (u.norm_eq_one k) (hperp k hk) x δ hq
  have h := WangZahlLot.Obl.wz_transverse_cell_weighted_cover.volume_le_of_coords
    u.orthonormal ![p, x, x] ![r, δ, δ] (tube δ x v ∩ ball p r) (by
      intro q hq k
      fin_cases k
      · have hn := abs_real_inner_le_norm (u 0) (q - p)
        rw [u.norm_eq_one, one_mul] at hn
        exact hn.trans (by simpa only [mem_ball, dist_eq_norm] using hq.2.le)
      · exact hc 1 (by decide) q hq.1
      · exact hc 2 (by decide) q hq.1)
  convert h using 1
  congr 1
  simp
  ring

/-- Uniform interior ball density of a container suffices to expand each tube shading. -/
lemma tube_shading_thickening {δ r lam A : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hlam : 0 ≤ lam) (hA : 0 ≤ A) {P Y : Set Space} (hP : MeasurableSet P)
    (hY : MeasurableSet Y) {x v : Space} (hv : ‖v‖ = 1)
    (hYT : Y ⊆ tube δ x v)
    (hden : ENNReal.ofReal (lam * δ ^ 2) ≤ volume Y)
    (hball : ∀ y ∈ Y, ENNReal.ofReal (A * r ^ 3) ≤ volume (P ∩ ball y r)) :
    ENNReal.ofReal ((A * lam / 8) * r ^ 2) ≤ volume (P ∩ thickening r Y) := by
  have hconv := thickening_volume_mul hP hY r (ENNReal.ofReal (A * r ^ 3))
    (ENNReal.ofReal (8 * r * δ ^ 2)) hball (fun p =>
      (measure_mono (Set.inter_subset_inter_left (ball p r) hYT)).trans (tube_ball_volume_le x v p hv))
  have hprod := (mul_le_mul' (le_refl (ENNReal.ofReal (A * r ^ 3))) hden).trans hconv
  apply (ENNReal.mul_le_mul_iff_right
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < 8 * r * δ ^ 2)).ne'
    ENNReal.ofReal_ne_top).mp
  convert hprod using 1
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end WangZahlLot.Obl.wz_frostman_quadratic_flat_gain.X264
