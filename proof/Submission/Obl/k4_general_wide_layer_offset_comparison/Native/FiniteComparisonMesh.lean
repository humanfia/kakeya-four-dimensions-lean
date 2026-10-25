-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/FiniteComparisonMesh.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/FiniteComparisonMesh.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ComparisonMesh
import Submission.Lib.K4AffineMeshCaps.Saturation

/-! Construction of finite comparison cells from an actual bounded original base map. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set
open Submission.Lib.K4AffineMeshCaps
open scoped ENNReal Classical

noncomputable section

def eucMeshCell (δ : ℝ) (q : Fin 3 → ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  WithLp.ofLp ⁻¹' meshBox δ q

theorem measurableSet_eucMeshCell (δ : ℝ) (q : Fin 3 → ℤ) :
    MeasurableSet (eucMeshCell δ q) :=
  (measurableSet_meshBox δ q).preimage (by fun_prop)

theorem volume_eucMeshCell {δ : ℝ} (hδ : 0 < δ) (q : Fin 3 → ℤ) :
    volume (eucMeshCell δ q) = ENNReal.ofReal (δ ^ 3) := by
  have hpres := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  change volume ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' meshBox δ q) = _
  rw [hpres.measure_preimage_equiv, volume_meshBox hδ]

theorem dist_le_eucMeshCell {δ : ℝ} (hδ : 0 < δ) (q : Fin 3 → ℤ)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ eucMeshCell δ q) (hy : y ∈ eucMeshCell δ q) :
    dist x y ≤ 3 * δ := by
  have hc : ∀ i : Fin 3, |(x - y) i| ≤ δ := by
    intro i
    exact meshBox_coordinate_distance hδ hx hy i
  have hs : ‖x - y‖ ^ 2 ≤ 3 * δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i : Fin 3, (x - y) i ^ 2 ≤ ∑ _i : Fin 3, δ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg ((x - y) i)) (hc i) 2
      _ = _ := by simp
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y), sq_nonneg δ]

/-- A bounded original base map has an actual finite comparison mesh. Its volume
budget is at most one, and every original finite-grid ceiling transfers without loss.
The code outside the original full-measure bounded set may be arbitrary. -/
theorem exists_finite_comparison_mesh {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3)) (hZ : Measurable Z)
    (hbound : ∀ᵐ p ∂μ, ‖Z p‖ ≤ 1 / 8) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 24) :
    ∃ M : ComparisonMesh μ, M.base = Z ∧ M.vol = ENNReal.ofReal (δ ^ 3) ∧
      M.diameter = 3 * δ ∧ (M.n : ℝ) * δ ^ 3 ≤ 1 ∧
      ∀ (A : ℝ≥0∞) (P : Ω → Prop),
        (∀ q : Fin 3 → ℤ, μ {p | baseMesh δ (WithLp.ofLp (Z p)) = q ∧ P p} ≤
          A * ENNReal.ofReal (δ ^ 3)) →
        ∀ q, μ {p | M.code p = q ∧ P p} ≤ A * M.vol := by
  obtain ⟨F, hF, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover hδ
    (by norm_num : (0 : ℝ) ≤ 1 / 8) 0
  let Q : Finset (Fin 3 → ℤ) := Fintype.piFinset fun _ => F
  have hzero : (fun _ : Fin 3 => (0 : ℤ)) ∈ Q := by
    apply Fintype.mem_piFinset.mpr
    intro i
    simpa using hcover 0 (by norm_num : |(0 : ℝ) - 0| ≤ 1 / 8)
  let q₀ : Q := ⟨fun _ => 0, hzero⟩
  let raw : Ω → Fin 3 → ℤ := fun p => baseMesh δ (WithLp.ofLp (Z p))
  have hraw : Measurable raw := (measurable_baseMesh δ).comp (by fun_prop)
  let clipped : Ω → Q := fun p =>
    ⟨if raw p ∈ Q then raw p else q₀.val, by split_ifs with h; exact h; exact q₀.property⟩
  have hclip : Measurable clipped := by
    apply Measurable.subtype_mk
    exact hraw.ite (hraw (Set.Finite.measurableSet Q.finite_toSet)) measurable_const
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  have hcoverae : ∀ᵐ p ∂μ, raw p ∈ Q := by
    filter_upwards [hbound] with p hp
    apply Fintype.mem_piFinset.mpr
    intro i
    apply hcover
    simp only [sub_zero]
    have hi : |(Z p) i| ≤ ‖Z p‖ := by simpa using PiLp.norm_apply_le (Z p) i
    exact hi.trans hp
  have hclipae : ∀ᵐ p ∂μ, (clipped p).val = raw p := by
    filter_upwards [hcoverae] with p hp
    simp only [clipped, if_pos hp]
  let M : ComparisonMesh μ :=
    { n := Fintype.card Q
      code := fun p => e (clipped p)
      measurable_code := (measurable_of_finite e).comp hclip
      base := Z
      measurable_base := hZ
      cell := fun q => eucMeshCell δ (e.symm q).val
      measurable_cell := fun q => measurableSet_eucMeshCell δ _
      disjoint_cell := by
        intro q q' hne
        apply Set.disjoint_left.mpr
        intro z hz hz'
        have heq : (e.symm q).val = (e.symm q').val := hz.symm.trans hz'
        exact hne (e.symm.injective (Subtype.ext heq))
      vol := ENNReal.ofReal (δ ^ 3)
      vol_ne_zero := by positivity
      vol_ne_top := ENNReal.ofReal_ne_top
      cell_volume := fun q => volume_eucMeshCell hδ _
      diameter := 3 * δ
      diameter_le := by linarith
      dist_le := fun q x hx y hy => dist_le_eucMeshCell hδ _ hx hy
      original := by
        filter_upwards [hbound, hclipae] with p hp hc
        refine ⟨hp, ?_⟩
        change raw p = (e.symm (e (clipped p))).val
        simpa only [Equiv.symm_apply_apply] using hc.symm }
  have hn : (M.n : ℝ) * δ ^ 3 ≤ 1 := by
    have hcard : Q.card = F.card ^ 3 := by simp [Q, Fintype.card_piFinset]
    have hscaled : (F.card : ℝ) * δ ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right hF hδ.le
      have heq : (4 * (1 / 8) / δ + 2) * δ = 1 / 2 + 2 * δ := by field_simp; ring
      rw [heq] at h
      linarith
    change (Fintype.card Q : ℝ) * δ ^ 3 ≤ 1
    rw [Fintype.card_coe, hcard, Nat.cast_pow]
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ F.card * δ) hscaled 3
    nlinarith only [h]
  refine ⟨M, rfl, rfl, rfl, hn, ?_⟩
  intro A P hcap q
  refine (measure_mono_ae ?_).trans (hcap (e.symm q).val)
  filter_upwards [hclipae] with p hp hmem
  refine ⟨?_, hmem.2⟩
  change raw p = (e.symm q).val
  have heq : clipped p = e.symm q := e.injective (by simpa only [Equiv.apply_symm_apply] using hmem.1)
  exact hp.symm.trans (congrArg Subtype.val heq)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
