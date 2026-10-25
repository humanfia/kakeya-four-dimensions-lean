-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/ComparisonIndexCaps.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ComparisonIndexCaps.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ComparisonMesh
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! Native-bin caps imply each current index-cell ceiling, with no current mass floor. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- A current index selects one graph with small native fitting error. Resolving the
graph on a comparison cell bounds that index's mass by six original scalar-bin caps.
The center is an actual current incidence when the event has positive mass. -/
theorem index_cell_cap_of_native_bins_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ComparisonMesh μ) {n : ℕ} (index : Ω → Fin n)
    (signal : Ω → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin 3) → ℂ)
    (K : NNReal) {a e R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    (hsmall : e + (K : ℝ) * M.diameter ≤ R)
    (hlip : ∀ i, LipschitzOnWith K (f i) (closedBall 0 (1 / 2)))
    (hfit : ∀ᵐ p ∂μ, ‖(signal p : ℂ) - f (index p) (M.base p)‖ ≤ e)
    (A : ℝ≥0∞)
    (hcap : ∀ q j, μ {p | M.code p = q ∧ ⌊signal p / a⌋ = j} ≤ A * M.vol)
    (q : Fin M.n) (i : Fin n) :
    μ {p | M.code p = q ∧ index p = i} ≤ ENNReal.ofReal (4 * R / a + 2) * A * M.vol := by
  classical
  by_cases hzero : μ {p | M.code p = q ∧ index p = i} = 0
  · rw [hzero]
    exact zero_le
  have hae : ∀ᵐ p ∂μ, (‖M.base p‖ ≤ 1 / 8 ∧ M.base p ∈ M.cell (M.code p)) ∧
      ‖(signal p : ℂ) - f (index p) (M.base p)‖ ≤ e := M.original.and hfit
  obtain ⟨p₀, hp₀, hgood₀, hfit₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hzero
    (hae.filter_mono (ae_mono Measure.restrict_le_self))
  have hbase₀ : M.base p₀ ∈ M.cell q := by simpa only [hp₀.1] using hgood₀.2
  have hnorm₀ : M.base p₀ ∈ closedBall 0 (1 / 2) := by
    rw [mem_closedBall_zero_iff]
    linarith [hgood₀.1]
  let center : ℝ := (f i (M.base p₀)).re
  obtain ⟨F, hF, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover ha hR center
  have hbound : ∀ᵐ p ∂μ, M.code p = q → index p = i → |signal p - center| ≤ R := by
    filter_upwards [hae] with p hp hq hi
    have hnorm : M.base p ∈ closedBall 0 (1 / 2) := by
      rw [mem_closedBall_zero_iff]
      linarith [hp.1.1]
    have hbase : M.base p ∈ M.cell q := by simpa only [hq] using hp.1.2
    have hdist : dist (M.base p) (M.base p₀) ≤ M.diameter := M.dist_le q _ hbase _ hbase₀
    have hgraph : ‖f i (M.base p) - f i (M.base p₀)‖ ≤ (K : ℝ) * M.diameter := by
      calc
        _ = dist (f i (M.base p)) (f i (M.base p₀)) := (dist_eq_norm _ _).symm
        _ ≤ (K : ℝ) * dist (M.base p) (M.base p₀) :=
          (hlip i).dist_le_mul _ hnorm _ hnorm₀
        _ ≤ _ := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
    have hreal : |signal p - (f i (M.base p)).re| ≤ e := by
      have h := (Complex.abs_re_le_norm ((signal p : ℂ) - f i (M.base p))).trans
        (by simpa only [hi] using hp.2)
      simpa only [Complex.sub_re, Complex.ofReal_re] using h
    have hrealgraph : |(f i (M.base p)).re - (f i (M.base p₀)).re| ≤ (K : ℝ) * M.diameter := by
      simpa only [Complex.sub_re] using
        (Complex.abs_re_le_norm (f i (M.base p) - f i (M.base p₀))).trans hgraph
    calc
      _ ≤ |signal p - (f i (M.base p)).re| + |(f i (M.base p)).re - center| := abs_sub_le _ _ _
      _ ≤ e + (K : ℝ) * M.diameter := add_le_add hreal hrealgraph
      _ ≤ R := hsmall
  have hsub : {p | M.code p = q ∧ index p = i} ≤ᵐ[μ]
      ⋃ j ∈ F, {p | M.code p = q ∧ ⌊signal p / a⌋ = j} := by
    filter_upwards [hbound] with p hp hmem
    exact mem_iUnion.mpr ⟨⌊signal p / a⌋,
      mem_iUnion.mpr ⟨hcover _ (hp hmem.1 hmem.2), hmem.1, rfl⟩⟩
  calc
    _ ≤ μ (⋃ j ∈ F, {p | M.code p = q ∧ ⌊signal p / a⌋ = j}) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ F, μ {p | M.code p = q ∧ ⌊signal p / a⌋ = j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ F, A * M.vol := Finset.sum_le_sum fun j _ => hcap q j
    _ = ENNReal.ofReal (F.card : ℝ) * A * M.vol := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hF) le_rfl) le_rfl

/-- The width-one version used for the two current color marginals. -/
theorem index_cell_cap_of_native_bins {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : ComparisonMesh μ) {n : ℕ} (index : Ω → Fin n)
    (signal : Ω → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin 3) → ℂ)
    (K : NNReal) {a e : ℝ} (ha : 0 < a)
    (hsmall : e + (K : ℝ) * M.diameter ≤ a)
    (hlip : ∀ i, LipschitzOnWith K (f i) (closedBall 0 (1 / 2)))
    (hfit : ∀ᵐ p ∂μ, ‖(signal p : ℂ) - f (index p) (M.base p)‖ ≤ e)
    (A : ℝ≥0∞)
    (hcap : ∀ q j, μ {p | M.code p = q ∧ ⌊signal p / a⌋ = j} ≤ A * M.vol)
    (q : Fin M.n) (i : Fin n) :
    μ {p | M.code p = q ∧ index p = i} ≤ 6 * A * M.vol := by
  have h := index_cell_cap_of_native_bins_radius μ M index signal f K ha ha.le hsmall hlip hfit A hcap q i
  have hconst : 4 * a / a + 2 = 6 := by field_simp; norm_num
  simpa only [hconst, ENNReal.ofReal_ofNat] using h


end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
