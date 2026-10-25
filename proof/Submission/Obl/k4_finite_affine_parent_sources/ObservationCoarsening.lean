-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Lib.K4MovingMeshBoxes.Geometry

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- A uniformly finite relation between two discrete observations transfers
an unchanged continuous-base ceiling. No bound on the integer labels is used. -/
theorem observation_cap_of_bin_cover {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (lam : Measure X) [SFinite lam]
    (base : Ω → X) (fine coarse : Ω → ℤ)
    (hf : Measurable (fun z => (base z, fine z)))
    (hc : Measurable (fun z => (base z, coarse z)))
    (C : ℝ≥0∞) (hcap : μ.map (fun z => (base z, fine z)) ≤
      C • (lam.prod Measure.count))
    (F : ℤ → Finset ℤ) (m : ℝ≥0∞) (hF : ∀ j, ((F j).card : ℝ≥0∞) ≤ m)
    (hcover : ∀ z, fine z ∈ F (coarse z)) :
    μ.map (fun z => (base z, coarse z)) ≤
      (m * C) • (lam.prod Measure.count) := by
  classical
  apply Measure.le_iff.mpr
  intro U hU
  let A (j : ℤ) : Set X := {x | (x, j) ∈ U}
  have hA (j : ℤ) : MeasurableSet (A j) :=
    hU.preimage (measurable_id.prodMk measurable_const)
  let V : Set (X × ℤ) := ⋃ j : ℤ, A j ×ˢ (F j : Set ℤ)
  have hV : MeasurableSet V :=
    MeasurableSet.iUnion fun j => (hA j).prod (F j).measurableSet
  have hsub : (fun z => (base z, coarse z)) ⁻¹' U ⊆
      (fun z => (base z, fine z)) ⁻¹' V := by
    intro z hz
    exact mem_iUnion.mpr ⟨coarse z, hz, hcover z⟩
  have href : (lam.prod Measure.count) U = ∑' j : ℤ, lam (A j) := by
    rw [Measure.prod_apply_symm hU, lintegral_count]
    rfl
  have hvol : (lam.prod Measure.count) V ≤ m * (lam.prod Measure.count) U := by
    calc
      _ ≤ ∑' j : ℤ, (lam.prod Measure.count) (A j ×ˢ (F j : Set ℤ)) :=
        measure_iUnion_le _
      _ = ∑' j : ℤ, lam (A j) * (F j).card := by simp only [Measure.prod_prod, Measure.count_apply_finset]
      _ ≤ ∑' j : ℤ, lam (A j) * m := by
        apply ENNReal.tsum_le_tsum
        intro j
        exact mul_le_mul' le_rfl (hF j)
      _ = (∑' j : ℤ, lam (A j)) * m := ENNReal.tsum_mul_right
      _ = _ := by rw [← href]; ring
  rw [Measure.map_apply hc hU, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ μ ((fun z => (base z, fine z)) ⁻¹' V) := measure_mono hsub
    _ = (μ.map (fun z => (base z, fine z))) V := (Measure.map_apply hf hV).symm
    _ ≤ (C • (lam.prod Measure.count)) V := hcap V
    _ = C * (lam.prod Measure.count) V := by rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ C * (m * (lam.prod Measure.count) U) := mul_le_mul' le_rfl hvol
    _ = _ := by ring

/-- Arbitrary unaligned hidden meshes preserve a continuous observation
ceiling with its explicit interval-cover cost. The source can already
be restricted to any fixed original angular bin. -/
theorem observation_cap_coarsen {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (lam : Measure X) [SFinite lam]
    (base : Ω → X) (value : Ω → ℝ) (hb : Measurable base) (hv : Measurable value)
    {fine coarse : ℝ} (hf : 0 < fine) (hc : 0 < coarse)
    (C : ℝ≥0∞) (hcap : μ.map (fun z => (base z, ⌊value z / fine⌋)) ≤
      C • (lam.prod Measure.count)) :
    μ.map (fun z => (base z, ⌊value z / coarse⌋)) ≤
      (ENNReal.ofReal (2 * coarse / fine + 2) * C) • (lam.prod Measure.count) := by
  classical
  choose F hF hcover using fun j : ℤ => interval_mesh_cover hf
    (show 0 ≤ coarse / 2 by positivity) (coarse * ((j : ℝ) + 1 / 2))
  have hFm (j : ℤ) : ((F j).card : ℝ≥0∞) ≤ ENNReal.ofReal (2 * coarse / fine + 2) := by
    have hh : ((F j).card : ℝ) ≤ 2 * coarse / fine + 2 :=
      (hF j).trans_eq (by ring)
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  have hcovers (z : Ω) : ⌊value z / fine⌋ ∈ F ⌊value z / coarse⌋ := by
    apply hcover
    have hlo := (le_div_iff₀ hc).mp (Int.floor_le (value z / coarse))
    have hhi := (div_lt_iff₀ hc).mp (Int.lt_floor_add_one (value z / coarse))
    rw [abs_le]
    constructor <;> nlinarith
  exact observation_cap_of_bin_cover μ lam base
    (fun z => ⌊value z / fine⌋) (fun z => ⌊value z / coarse⌋)
    (hb.prodMk (Int.measurable_floor.comp (hv.div_const fine)))
    (hb.prodMk (Int.measurable_floor.comp (hv.div_const coarse))) C hcap F _ hFm hcovers

/-- The continuous observation ceiling costs at most six when the new
hidden mesh is at most twice the old one, without any alignment premise. -/
theorem observation_cap_coarsen_two {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (lam : Measure X) [SFinite lam]
    (base : Ω → X) (value : Ω → ℝ) (hb : Measurable base) (hv : Measurable value)
    {fine coarse : ℝ} (hf : 0 < fine) (hc : 0 < coarse) (hcf : coarse ≤ 2 * fine)
    (C : ℝ≥0∞) (hcap : μ.map (fun z => (base z, ⌊value z / fine⌋)) ≤
      C • (lam.prod Measure.count)) :
    μ.map (fun z => (base z, ⌊value z / coarse⌋)) ≤
      (6 * C) • (lam.prod Measure.count) := by
  apply (observation_cap_coarsen μ lam base value hb hv hf hc C hcap).trans
  have hratio : coarse / fine ≤ 2 := (div_le_iff₀ hf).mpr hcf
  have hm : ENNReal.ofReal (2 * coarse / fine + 2) ≤ (6 : ℝ≥0∞) := by
    apply (ENNReal.ofReal_le_ofReal (show 2 * coarse / fine + 2 ≤ 6 by rw [mul_div_assoc]; linarith)).trans_eq
    norm_num
  apply Measure.le_iff'.mpr
  intro U
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' (mul_le_mul' hm le_rfl) le_rfl

end
end Submission.Obl.k4_finite_affine_parent_sources
