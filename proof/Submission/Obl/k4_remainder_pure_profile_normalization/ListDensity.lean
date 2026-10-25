/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/ListDensity.lean.
-/
import Submission.Lib.K4Homogenization.DensityOperations

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory Set
open scoped ENNReal

/-- Known lists replace the total number of chart labels in the refinement
low-density bound.  The lists need not themselves be measurable: all integrated
functions are the given measurable densities.  The support assertion is stated
almost everywhere, so arbitrary measurable RN versions can be used.
-/
theorem list_refinement_lowDensity_mass {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (ε D : ENNReal) (f : X → ENNReal) (g : ι → X → ENNReal)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i)) (L : X → Finset ι)
    (hcard : ∀ x, ((L x).card : ENNReal) ≤ D)
    (hsupport : ∀ᵐ x ∂μ, ∀ i, i ∉ L x → g i x = 0) :
    (∑ i, ∫⁻ x in Submission.Lib.K4Homogenization.lowDensity ε f (g i), g i x ∂μ) ≤
      ε * D * ∫⁻ x, f x ∂μ := by
  classical
  let G (i : ι) (x : X) :=
    (Submission.Lib.K4Homogenization.lowDensity ε f (g i)).indicator (g i) x
  have hG (i : ι) : Measurable (G i) :=
    (hg i).indicator (Submission.Lib.K4Homogenization.measurableSet_lowDensity ε hf (hg i))
  have hterm (i : ι) :
      (∫⁻ x in Submission.Lib.K4Homogenization.lowDensity ε f (g i), g i x ∂μ) =
        ∫⁻ x, G i x ∂μ := by
    exact (lintegral_indicator
      (Submission.Lib.K4Homogenization.measurableSet_lowDensity ε hf (hg i)) (g i)).symm
  have hpoint : ∀ᵐ x ∂μ, (∑ i, G i x) ≤ (ε * D) * f x := by
    filter_upwards [hsupport] with x hx
    have hsum : (∑ i, G i x) = ∑ i ∈ L x, G i x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [G, Set.indicator_apply, hx i hi, ite_self]
    calc
      (∑ i, G i x) = ∑ i ∈ L x, G i x := hsum
      _ ≤ ∑ _i ∈ L x, ε * f x := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : x ∈ Submission.Lib.K4Homogenization.lowDensity ε f (g i)
        · exact (Set.indicator_of_mem hi _).trans_le hi.le
        · simp only [G, Set.indicator_of_notMem hi, zero_le]
      _ = ((L x).card : ENNReal) * (ε * f x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * (ε * f x) := mul_le_mul' (hcard x) le_rfl
      _ = (ε * D) * f x := by ring
  simp_rw [hterm]
  calc
    (∑ i, ∫⁻ x, G i x ∂μ) = ∫⁻ x, ∑ i, G i x ∂μ := by
      rw [lintegral_finsetSum _ (fun i _ => hG i)]
    _ ≤ ∫⁻ x, (ε * D) * f x ∂μ := lintegral_mono_ae hpoint
    _ = (ε * D) * ∫⁻ x, f x ∂μ := lintegral_const_mul _ hf

/-- Pull the same list-size refinement estimate back to the actual incidence
laws, with independently chosen measurable densities for the chart labels. -/
theorem observation_list_refinement_lowDensity_mass {X ι : Type*}
    [MeasurableSpace X] [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (m : (i : ι) → Measure (Ω i)) (μ : Measure X)
    (obs : (i : ι) → Ω i → X) (hobs : ∀ i, Measurable (obs i))
    (ε D : ENNReal) (f : X → ENNReal) (g : ι → X → ENNReal)
    (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (m i).map (obs i) = μ.withDensity (g i))
    (L : X → Finset ι) (hcard : ∀ x, ((L x).card : ENNReal) ≤ D)
    (hsupport : ∀ᵐ x ∂μ, ∀ i, i ∉ L x → g i x = 0) :
    (∑ i, m i {a | g i (obs i a) < ε * f (obs i a)}) ≤
      ε * D * ∫⁻ x, f x ∂μ := by
  have heq (i : ι) : m i {a | g i (obs i a) < ε * f (obs i a)} =
      ∫⁻ x in Submission.Lib.K4Homogenization.lowDensity ε f (g i), g i x ∂μ := by
    have hset := Submission.Lib.K4Homogenization.measurableSet_lowDensity ε hf (hg i)
    change m i ((obs i) ⁻¹' Submission.Lib.K4Homogenization.lowDensity ε f (g i)) = _
    rw [← Measure.map_apply (hobs i) hset, hlaw i, withDensity_apply _ hset]
  simp_rw [heq]
  exact list_refinement_lowDensity_mass μ ε D f g hf hg L hcard hsupport

/-- Obtain the density support assertion from lists on the actual incidences.
Only the observation images of the selected events need to be measurable; the
arbitrary original lists need no measurability assumption.
-/
theorem refined_density_support_of_images {X ι : Type*}
    [MeasurableSpace X] [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (m : (i : ι) → Measure (Ω i)) (μ : Measure X)
    (obs : (i : ι) → Ω i → X) (hobs : ∀ i, Measurable (obs i))
    (g : ι → X → ENNReal) (hg : ∀ i, Measurable (g i))
    (hlaw : ∀ i, (m i).map (obs i) = μ.withDensity (g i))
    (F : (i : ι) → Set (Ω i)) (hsupport : ∀ i, m i (F i)ᶜ = 0)
    (himage : ∀ i, MeasurableSet (obs i '' F i))
    (L : X → Finset ι) (hlabel : ∀ i a, a ∈ F i → i ∈ L (obs i a)) :
    ∀ᵐ x ∂μ, ∀ i, i ∉ L x → g i x = 0 := by
  have hzero (i : ι) : ∀ᵐ x ∂μ, x ∉ obs i '' F i → g i x = 0 := by
    have hz : (m i).map (obs i) (obs i '' F i)ᶜ = 0 := by
      rw [Measure.map_apply (hobs i) (himage i).compl]
      apply le_antisymm _ zero_le
      calc
        m i ((obs i) ⁻¹' (obs i '' F i)ᶜ) ≤ m i (F i)ᶜ := by
          apply measure_mono
          intro a ha haF
          exact ha ⟨a, haF, rfl⟩
        _ = 0 := hsupport i
    rw [hlaw i, withDensity_apply _ (himage i).compl] at hz
    exact (ae_restrict_iff' (himage i).compl).mp ((lintegral_eq_zero_iff (hg i)).mp hz)
  filter_upwards [ae_all_iff.mpr hzero] with x hx
  intro i hi
  apply hx i
  intro himage
  obtain ⟨a, ha, hax⟩ := himage
  exact hi (hax ▸ hlabel i a ha)

end Submission.Obl.k4_remainder_pure_profile_normalization
