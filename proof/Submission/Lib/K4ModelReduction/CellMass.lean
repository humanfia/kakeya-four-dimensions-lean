import Submission.Lib.K4ModelReduction.CellAveraging

/-!
Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper.
 Mass preservation and contraction for uniform mesh-cell redistribution. -/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Set
open scoped ENNReal

def halfOpenMeshCell (ρ x : ℝ) : Set ℝ :=
  Ico (ρ * (⌊x / ρ⌋ : ℝ)) (ρ * (⌊x / ρ⌋ : ℝ) + ρ)

theorem halfOpenMeshCell_ae_eq (ρ x : ℝ) :
    halfOpenMeshCell ρ x =ᵐ[volume] meshCell ρ x := Ico_ae_eq_Icc

theorem mem_halfOpenMeshCell_iff {ρ x y : ℝ} (hρ : 0 < ρ) :
    y ∈ halfOpenMeshCell ρ x ↔ ⌊y / ρ⌋ = ⌊x / ρ⌋ := by
  rw [Int.floor_eq_iff]
  change (ρ * (⌊x / ρ⌋ : ℝ) ≤ y ∧ y < ρ * (⌊x / ρ⌋ : ℝ) + ρ) ↔ _
  rw [le_div_iff₀ hρ, div_lt_iff₀ hρ]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem halfOpenMeshCell_symm {ρ x y : ℝ} (hρ : 0 < ρ) :
    y ∈ halfOpenMeshCell ρ x ↔ x ∈ halfOpenMeshCell ρ y := by
  simp only [mem_halfOpenMeshCell_iff hρ, eq_comm]

/-- The nonnegative version of uniform redistribution inside mesh cells. -/
noncomputable def meshLinAverage (f : ℝ → ℝ≥0∞) (ρ x : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ρ)⁻¹ * ∫⁻ y in halfOpenMeshCell ρ x, f y

theorem meshLinAverage_mass (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x, meshLinAverage f ρ x = ∫⁻ x, f x := by
  classical
  let S : Set (ℝ × ℝ) := {z | z.2 ∈ halfOpenMeshCell ρ z.1}
  have hanchor : Measurable (fun z : ℝ × ℝ => ρ * (⌊z.1 / ρ⌋ : ℝ)) := by
    fun_prop
  have hS : MeasurableSet S :=
    (measurableSet_le hanchor measurable_snd).inter
      (measurableSet_lt measurable_snd (hanchor.add_const ρ))
  have hG : Measurable (S.indicator (fun z : ℝ × ℝ => f z.2)) :=
    (hf.comp measurable_snd).indicator hS
  have hrow (x : ℝ) :
      (∫⁻ y, S.indicator (fun z : ℝ × ℝ => f z.2) (x, y)) =
      ∫⁻ y in halfOpenMeshCell ρ x, f y := by
    have hm : MeasurableSet (halfOpenMeshCell ρ x) := measurableSet_Ico
    rw [← lintegral_indicator hm]
    congr 1
  have hcol (y : ℝ) :
      (∫⁻ x, S.indicator (fun z : ℝ × ℝ => f z.2) (x, y)) =
      f y * ENNReal.ofReal ρ := by
    have heq : (fun x => S.indicator (fun z : ℝ × ℝ => f z.2) (x, y)) =
        (halfOpenMeshCell ρ y).indicator (fun _ => f y) := by
      funext x
      change (if y ∈ halfOpenMeshCell ρ x then f y else 0) =
        (if x ∈ halfOpenMeshCell ρ y then f y else 0)
      rw [halfOpenMeshCell_symm hρ]
    have hm : MeasurableSet (halfOpenMeshCell ρ y) := measurableSet_Ico
    rw [heq, lintegral_indicator_const hm]
    congr 1
    rw [halfOpenMeshCell, Real.volume_Ico]
    congr 1
    ring
  calc
    _ = (ENNReal.ofReal ρ)⁻¹ * ∫⁻ x, ∫⁻ y in halfOpenMeshCell ρ x, f y := by
      exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by positivity))
    _ = (ENNReal.ofReal ρ)⁻¹ * ∫⁻ y, f y * ENNReal.ofReal ρ := by
      congr 1
      simp_rw [← hrow]
      rw [lintegral_lintegral_swap (f := fun (x y : ℝ) =>
        S.indicator (fun z : ℝ × ℝ => f z.2) (x, y)) hG.aemeasurable]
      simp_rw [hcol]
    _ = (ENNReal.ofReal ρ)⁻¹ * ((∫⁻ y, f y) * ENNReal.ofReal ρ) := by
      rw [lintegral_mul_const _ hf]
    _ = _ := by
      rw [mul_comm (∫⁻ y, f y), ← mul_assoc,
        ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]

theorem meshAverage_abs_le_meshLinAverage (f : ℝ → ℝ) {ρ : ℝ}
    (_hρ : 0 < ρ) (x : ℝ) :
    ENNReal.ofReal |meshAverage f ρ x| ≤
      meshLinAverage (fun y => ENNReal.ofReal |f y|) ρ x := by
  have hmeasure : ProbabilityTheory.cond volume (meshCell ρ x) =
      (ENNReal.ofReal ρ)⁻¹ • volume.restrict (halfOpenMeshCell ρ x) := by
    rw [ProbabilityTheory.cond, meshCell_volume,
      Measure.restrict_congr_set (halfOpenMeshCell_ae_eq ρ x)]
  calc
    _ = ‖∫ y, f y ∂ProbabilityTheory.cond volume (meshCell ρ x)‖ₑ :=
      (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ y, ‖f y‖ₑ ∂ProbabilityTheory.cond volume (meshCell ρ x) :=
      enorm_integral_le_lintegral_enorm f
    _ = _ := by
      rw [hmeasure, lintegral_smul_measure]
      simp only [Real.enorm_eq_ofReal_abs, meshLinAverage, smul_eq_mul]

/-- Uniform redistribution is an L1 contraction, including on functions
whose global L1 norm is infinite. -/
theorem meshAverage_lintegral_abs_le (f : ℝ → ℝ) (hf : Measurable f)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x, ENNReal.ofReal |meshAverage f ρ x| ≤ ∫⁻ x, ENNReal.ofReal |f x| := by
  exact (lintegral_mono (meshAverage_abs_le_meshLinAverage f hρ)).trans_eq
    (meshLinAverage_mass _ (ENNReal.measurable_ofReal.comp hf.abs) hρ)

theorem integrable_meshCellLaw (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hbound : ∀ y, |f y| ≤ M) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    Integrable f (ProbabilityTheory.cond volume (meshCell ρ x)) := by
  have := meshCell_law_isProbabilityMeasure hρ x
  exact Integrable.of_bound hf.stronglyMeasurable.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hbound y)

theorem meshAverage_sub (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M L : ℝ) (hfbound : ∀ y, |f y| ≤ M) (hgbound : ∀ y, |g y| ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    meshAverage (fun y => f y - g y) ρ x = meshAverage f ρ x - meshAverage g ρ x :=
  integral_sub (integrable_meshCellLaw f hf M hfbound hρ x)
    (integrable_meshCellLaw g hg L hgbound hρ x)

theorem meshAverage_lintegral_abs_sub_le (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (M L : ℝ) (hfbound : ∀ y, |f y| ≤ M) (hgbound : ∀ y, |g y| ≤ L)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x, ENNReal.ofReal |meshAverage f ρ x - meshAverage g ρ x| ≤
      ∫⁻ x, ENNReal.ofReal |f x - g x| := by
  simpa only [meshAverage_sub f g hf hg M L hfbound hgbound hρ] using
    meshAverage_lintegral_abs_le (fun y => f y - g y) (hf.sub hg) hρ

theorem meshAverage_ofReal (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hbound : ∀ y, |f y| ≤ M) (hnonneg : ∀ y, 0 ≤ f y)
    {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    ENNReal.ofReal (meshAverage f ρ x) =
      meshLinAverage (fun y => ENNReal.ofReal (f y)) ρ x := by
  rw [meshAverage, ofReal_integral_eq_lintegral_ofReal
    (integrable_meshCellLaw f hf M hbound hρ x) (Filter.Eventually.of_forall hnonneg)]
  rw [meshLinAverage, ProbabilityTheory.cond, meshCell_volume, lintegral_smul_measure,
    Measure.restrict_congr_set (halfOpenMeshCell_ae_eq ρ x)]
  rfl

/-- Real nonnegative density redistribution preserves total mass. -/
theorem meshAverage_mass (f : ℝ → ℝ) (hf : Measurable f)
    (M : ℝ) (hbound : ∀ y, |f y| ≤ M) (hnonneg : ∀ y, 0 ≤ f y)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x, ENNReal.ofReal (meshAverage f ρ x) = ∫⁻ x, ENNReal.ofReal (f x) := by
  simp_rw [meshAverage_ofReal f hf M hbound hnonneg hρ]
  exact meshLinAverage_mass _ (ENNReal.measurable_ofReal.comp hf) hρ

end Submission.Lib.K4ModelReduction
