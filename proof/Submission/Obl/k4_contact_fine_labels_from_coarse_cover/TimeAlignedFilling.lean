-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/TimeAlignedFilling.lean
import Submission.Lib.K4AffineMeshCaps
import Mathlib.Tactic.FinCases

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open Set MeasureTheory Matrix
open Submission.Lib.K4AffineMeshCaps

noncomputable def timeMatrix (q : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![q⁻¹, 1, 1]

noncomputable def timeOffset (t₀ q : ℝ) : Fin 3 → ℝ := ![-t₀ / q, 0, 0]

noncomputable def timeFrame (t₀ q : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  affineBase (timeMatrix q) (timeOffset t₀ q) z

theorem timeFrame_zero (t₀ q : ℝ) (z : Fin 3 → ℝ) :
    timeFrame t₀ q z 0 = (z 0 - t₀) / q := by
  simp [timeFrame, timeMatrix, timeOffset, affineBase, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, div_eq_mul_inv]
  ring

theorem timeFrame_one (t₀ q : ℝ) (z : Fin 3 → ℝ) : timeFrame t₀ q z 1 = z 1 := by
  simp [timeFrame, timeMatrix, timeOffset, affineBase, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

theorem timeFrame_two (t₀ q : ℝ) (z : Fin 3 → ℝ) : timeFrame t₀ q z 2 = z 2 := by
  simp [timeFrame, timeMatrix, timeOffset, affineBase, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

theorem timeMatrix_det (q : ℝ) : (timeMatrix q).det = q⁻¹ := by
  simp [timeMatrix, Matrix.det_diagonal, Fin.prod_univ_three]

/-- A reciprocal integer mesh respects the unit time interval exactly. -/
theorem unit_mesh_bin_mem_unit {M : ℕ} (hM : 0 < M) {x y : ℝ}
    (hy : y ∈ Ico (0 : ℝ) 1)
    (hbin : ⌊x / (M : ℝ)⁻¹⌋ = ⌊y / (M : ℝ)⁻¹⌋) : x ∈ Ico (0 : ℝ) 1 := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  simp only [div_inv_eq_mul] at hbin
  have hx := Int.floor_eq_iff.mp hbin
  have hj₀ : (0 : ℤ) ≤ ⌊y * (M : ℝ)⌋ := Int.floor_nonneg.mpr (mul_nonneg hy.1 hMp.le)
  have hyM : y * (M : ℝ) < M := by simpa only [one_mul] using mul_lt_mul_of_pos_right hy.2 hMp
  have hj₁ : ⌊y * (M : ℝ)⌋ < (M : ℤ) := Int.floor_lt.mpr (by exact_mod_cast hyM)
  have hj₀' : (0 : ℝ) ≤ (⌊y * (M : ℝ)⌋ : ℤ) := by exact_mod_cast hj₀
  have hj₁' : ((⌊y * (M : ℝ)⌋ : ℤ) : ℝ) + 1 ≤ M := by
    exact_mod_cast Int.add_one_le_iff.mpr hj₁
  constructor
  · have h := div_nonneg (hj₀'.trans hx.1) hMp.le
    simpa [hMp.ne'] using h
  · have h := (div_lt_div_iff_of_pos_right hMp).mpr (hx.2.trans_le hj₁')
    simpa [hMp.ne'] using h

/-- Original fine-cell caps survive time normalization with its exact
Jacobian and any original incidence restriction. -/
theorem time_frame_mesh_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (C : Set Ω)
    {t₀ q δ σ B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hδ : 0 < δ) (hσ : 0 < σ) (hB : 0 ≤ B) (hresolve : δ / q ≤ σ)
    (hcap : ∀ r : Fin 3 → ℤ,
      μ {u | baseMesh δ (Z u) = r ∧ u ∈ C} ≤ ENNReal.ofReal (B * δ ^ 3))
    (r : Fin 3 → ℤ) :
    μ {u | baseMesh σ (timeFrame t₀ q (Z u)) = r ∧ u ∈ C} ≤
      ENNReal.ofReal (27 * B * q * σ ^ 3) := by
  have hδσ : δ ≤ σ := by
    apply le_trans _ hresolve
    apply (le_div_iff₀ hq).mpr
    exact mul_le_of_le_one_right hδ.le hq1
  have hrows : ∀ i : Fin 3, (∑ j, |timeMatrix q i j| * δ) ≤ σ := by
    intro i
    fin_cases i
    · simpa [timeMatrix, Fin.sum_univ_three, abs_of_pos (inv_pos.mpr hq),
        div_eq_mul_inv, mul_comm] using hresolve
    · simpa [timeMatrix, Fin.sum_univ_three] using hδσ
    · simpa [timeMatrix, Fin.sum_univ_three] using hδσ
  have h := affine_mesh_cell_cap μ Z (fun u => u ∈ C)
    (timeMatrix q) (timeOffset t₀ q)
    (by rw [timeMatrix_det]; exact inv_ne_zero hq.ne') hδ hσ hB hrows hcap r
  simpa only [timeFrame, timeMatrix_det, abs_of_pos (inv_pos.mpr hq), inv_inv] using h

/-- A time-aligned occupied mesh region supplies original volume filling
and actual nearby witnesses. The original law is never replaced by volume. -/
theorem exists_time_aligned_filling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (C : Set Ω)
    {t₀ q δ B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (M : ℕ) (hM : 0 < M) (hresolve : δ / q ≤ (M : ℝ)⁻¹)
    (htime : ∀ u ∈ C, Z u 0 ∈ Ico t₀ (t₀ + q))
    (hcap : ∀ r : Fin 3 → ℤ,
      μ {u | baseMesh δ (Z u) = r ∧ u ∈ C} ≤ ENNReal.ofReal (B * δ ^ 3)) :
    ∃ E : Set (Fin 3 → ℝ), MeasurableSet E ∧
      (∀ z ∈ E, z 0 ∈ Icc t₀ (t₀ + q)) ∧
      μ C ≤ ENNReal.ofReal (27 * B) * volume E ∧
      ∀ z ∈ E, ∃ u ∈ C, ∀ i, |z i - Z u i| ≤ (M : ℝ)⁻¹ := by
  let σ : ℝ := (M : ℝ)⁻¹
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hσ : 0 < σ := inv_pos.mpr hMp
  let S : Set (Fin 3 → ℝ) := (fun u => timeFrame t₀ q (Z u)) '' C
  let D := meshSaturation σ S
  let E := timeFrame t₀ q ⁻¹' D
  have hD : MeasurableSet D := measurableSet_meshSaturation _ _
  have hE : MeasurableSet E := (measurable_affineBase (timeMatrix q) (timeOffset t₀ q)) hD
  have hcaps := time_frame_mesh_cap (t₀ := t₀) μ Z C hq hq1 hδ hσ hB hresolve hcap
  have hCeq : {u | timeFrame t₀ q (Z u) ∈ S ∧ u ∈ C} = C := by
    ext u
    exact ⟨fun hu => hu.2, fun hu => ⟨⟨u, hu, rfl⟩, hu⟩⟩
  have hmass : μ C ≤ ENNReal.ofReal (27 * B * q) * volume D := by
    have h := measure_le_meshSaturation_volume μ (fun u => timeFrame t₀ q (Z u))
      (fun u => u ∈ C) hσ (by positivity : 0 ≤ 27 * B * q) hcaps S
    rwa [hCeq] at h
  have hvol : volume E = ENNReal.ofReal q * volume D := by
    change volume (affineBase (timeMatrix q) (timeOffset t₀ q) ⁻¹' D) = _
    have h := volume_affineBase_preimage (timeMatrix q) (timeOffset t₀ q)
      (by rw [timeMatrix_det]; exact inv_ne_zero hq.ne') D hD
    simpa only [timeMatrix_det, abs_of_pos (inv_pos.mpr hq), inv_inv] using h
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · intro z hz
    change timeFrame t₀ q z ∈ meshSaturation σ S at hz
    rw [meshSaturation] at hz
    obtain ⟨r, hr⟩ := mem_iUnion.mp hz
    unfold selectedMeshCell at hr
    split_ifs at hr with has
    · obtain ⟨w, hw, hcode⟩ := has
      obtain ⟨u, hu, rfl⟩ := hw
      have hbin : ⌊timeFrame t₀ q z 0 / (M : ℝ)⁻¹⌋ =
          ⌊timeFrame t₀ q (Z u) 0 / (M : ℝ)⁻¹⌋ :=
        (congrFun hr 0).trans (congrFun hcode 0).symm
      have hunit : timeFrame t₀ q (Z u) 0 ∈ Ico (0 : ℝ) 1 := by
        rw [timeFrame_zero]
        refine ⟨div_nonneg (sub_nonneg.mpr (htime u hu).1) hq.le, ?_⟩
        exact (div_lt_one hq).mpr (by linarith [(htime u hu).2])
      have hzunit := unit_mesh_bin_mem_unit hM hunit hbin
      rw [timeFrame_zero] at hzunit
      constructor
      · have h := (le_div_iff₀ hq).mp hzunit.1
        linarith
      · have h := (div_lt_one hq).mp hzunit.2
        linarith
    · exact hr.elim
  · apply hmass.trans_eq
    rw [hvol, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 27 * B)]
  · intro z hz
    obtain ⟨w, hw, hclose⟩ := meshSaturation_close hσ S hz
    obtain ⟨u, hu, rfl⟩ := hw
    change ∀ i, |timeFrame t₀ q z i - timeFrame t₀ q (Z u) i| ≤ σ at hclose
    refine ⟨u, hu, ?_⟩
    have h₀ := hclose 0
    rw [timeFrame_zero, timeFrame_zero] at h₀
    have heq : (z 0 - t₀) / q - (Z u 0 - t₀) / q = (z 0 - Z u 0) / q := by ring
    rw [heq, abs_div, abs_of_pos hq] at h₀
    have h₀' : |z 0 - Z u 0| ≤ σ :=
      ((div_le_iff₀ hq).mp h₀).trans (mul_le_of_le_one_right hσ.le hq1)
    intro i
    fin_cases i
    · exact h₀'
    · simpa [timeFrame_one, σ] using hclose 1
    · simpa [timeFrame_two, σ] using hclose 2

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
