import Submission.Lib.K4Homogenization.DensityOperations

/-! Observation lists need not be measurable. Disintegration still bounds the
number of nonzero restricted densities at almost every observation. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

section Conditional

variable {Ω Y ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace Y] [MeasurableEq Y]

/-- Conditional laws of the incidence, given its observation, live on the actual fiber. -/
theorem conditional_fiber_ae (μ : Measure Ω) [IsFiniteMeasure μ]
    (obs : Ω → Y) (hobs : Measurable obs) :
    ∀ᵐ y ∂μ.map obs, ∀ᵐ p ∂condDistrib id obs μ y, obs p = y := by
  have hg : ∀ᵐ z ∂μ.map (fun p => (obs p, p)), obs z.2 = z.1 := by
    apply (ae_map_iff (hobs.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hobs.comp measurable_snd) measurable_fst)).mpr
    exact ae_of_all _ fun _ => rfl
  change ∀ᵐ z ∂μ.map (fun p => (obs p, id p)), obs z.2 = z.1 at hg
  rw [← compProd_map_condDistrib hobs.aemeasurable aemeasurable_id] at hg
  exact Measure.ae_ae_of_ae_compProd hg

/-- The conditional probabilities of listed events can only be positive at listed labels. -/
theorem conditional_list_support (μ : Measure Ω) [IsFiniteMeasure μ]
    (obs : Ω → Y) (hobs : Measurable obs) (E : ι → Set Ω)
    (lst : Y → Finset ι) (hlist : ∀ i p, p ∈ E i → i ∈ lst (obs p)) :
    ∀ᵐ y ∂μ.map obs, ∀ i, condDistrib id obs μ y (E i) ≠ 0 → i ∈ lst y := by
  filter_upwards [conditional_fiber_ae μ obs hobs] with y hy
  intro i hi
  by_contra hnot
  have hz : condDistrib id obs μ y (E i) = 0 := by
    apply measure_mono_null (t := {p | obs p ≠ y})
    · intro p hp hpy
      exact hnot (hpy ▸ hlist i p hp)
    · exact hy
  exact hi hz

/-- A concrete measurable density for any measurable incidence restriction. -/
theorem conditional_restriction_density (μ : Measure Ω) [IsFiniteMeasure μ]
    (obs : Ω → Y) (hobs : Measurable obs) (ρ : Measure Y)
    (g : Y → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ρ.withDensity g)
    (E : Set Ω) (hE : MeasurableSet E) :
    (μ.restrict E).map obs = ρ.withDensity (fun y =>
      g y * condDistrib id obs μ y E) := by
  ext S hS
  rw [Measure.map_apply hobs hS, Measure.restrict_apply (hobs hS),
    withDensity_apply _ hS]
  have hκ : Measurable (fun y => condDistrib id obs μ y E) := Kernel.measurable_coe _ hE
  calc
    μ (obs ⁻¹' S ∩ E) = ∫⁻ p in obs ⁻¹' S, condDistrib id obs μ (obs p) E ∂μ :=
      (setLIntegral_preimage_condDistrib hobs aemeasurable_id hE hS).symm
    _ = ∫⁻ y in S, condDistrib id obs μ y E ∂μ.map obs :=
      (setLIntegral_map hS hκ hobs).symm
    _ = ∫⁻ y in S, g y * condDistrib id obs μ y E ∂ρ := by
      rw [hlaw]
      exact setLIntegral_withDensity_eq_setLIntegral_mul ρ hg hκ hS

end Conditional

/-- The refinement loss is the number of possible positive densities at each
observation, even if the policy witnessing that number is not measurable. -/
theorem listed_lowDensity_mass {Y ι : Type*} [MeasurableSpace Y] [Fintype ι]
    (ρ : Measure Y) (ε K : ENNReal) (g : Y → ENNReal) (h : ι → Y → ENNReal)
    (hg : Measurable g) (hh : ∀ i, Measurable (h i))
    (hsupport : ∀ᵐ y ∂ρ, ∃ L : Finset ι,
      (L.card : ENNReal) ≤ K ∧ ∀ i, h i y ≠ 0 → i ∈ L) :
    (∑ i, ∫⁻ y in Submission.Lib.K4Homogenization.lowDensity ε g (h i), h i y ∂ρ) ≤
      ε * K * ∫⁻ y, g y ∂ρ := by
  classical
  let B : ι → Set Y := fun i => Submission.Lib.K4Homogenization.lowDensity ε g (h i)
  have hBm : ∀ i, MeasurableSet (B i) := fun i =>
    Submission.Lib.K4Homogenization.measurableSet_lowDensity ε hg (hh i)
  have hpoint : (fun y => ∑ i, (B i).indicator (h i) y) ≤ᵐ[ρ]
      fun y => ε * K * g y := by
    filter_upwards [hsupport] with y hy
    obtain ⟨L, hL, hpos⟩ := hy
    have hsub : (∑ i ∈ L, (B i).indicator (h i) y) =
        ∑ i, (B i).indicator (h i) y := by
      apply Finset.sum_subset (Finset.subset_univ L)
      intro i _ hi
      have hz : h i y = 0 := by_contra fun hn => hi (hpos i hn)
      simp [hz, Set.indicator]
    calc
      _ = ∑ i ∈ L, (B i).indicator (h i) y := hsub.symm
      _ ≤ ∑ _i ∈ L, ε * g y := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : y ∈ B i
        · rw [indicator_of_mem hi]
          exact (show h i y < ε * g y from hi).le
        · rw [indicator_of_notMem hi]
          exact zero_le
      _ = (L.card : ENNReal) * (ε * g y) := by simp [nsmul_eq_mul]
      _ ≤ K * (ε * g y) := mul_le_mul' hL le_rfl
      _ = ε * K * g y := by ring
  calc
    _ = ∑ i, ∫⁻ y, (B i).indicator (h i) y ∂ρ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (lintegral_indicator (hBm i) (h i)).symm
    _ = ∫⁻ y, ∑ i, (B i).indicator (h i) y ∂ρ :=
      (lintegral_finsetSum _ (fun i _ => (hh i).indicator (hBm i))).symm
    _ ≤ ∫⁻ y, ε * K * g y ∂ρ := lintegral_mono_ae hpoint
    _ = _ := lintegral_const_mul _ hg

section ObservationLists

variable {Ω Y ι : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [MeasurableSpace Y] [MeasurableEq Y] [Fintype ι]

/-- Any measurable versions of the restricted densities respect the original
possibly nonmeasurable label policy almost everywhere. -/
theorem observation_list_density_support (μ : Measure Ω) [IsFiniteMeasure μ]
    (obs : Ω → Y) (hobs : Measurable obs) (ρ : Measure Y) [SigmaFinite ρ]
    (g : Y → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ρ.withDensity g)
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (h : ι → Y → ENNReal) (hh : ∀ i, Measurable (h i))
    (hrestrict : ∀ i, (μ.restrict (E i)).map obs = ρ.withDensity (h i))
    (lst : Y → Finset ι) (hlist : ∀ i p, p ∈ E i → i ∈ lst (obs p)) :
    ∀ᵐ y ∂ρ, ∀ i, h i y ≠ 0 → i ∈ lst y := by
  have hcond := conditional_list_support μ obs hobs E lst hlist
  rw [hlaw, ae_withDensity_iff hg] at hcond
  have heq : ∀ᵐ y ∂ρ, ∀ i,
      h i y = g y * condDistrib id obs μ y (E i) := by
    apply ae_all_iff.mpr
    intro i
    apply (withDensity_eq_iff_of_sigmaFinite (hh i).aemeasurable
      (hg.mul (Kernel.measurable_coe _ (hE i))).aemeasurable).mp
    exact (hrestrict i).symm.trans
      (conditional_restriction_density μ obs hobs ρ g hg hlaw (E i) (hE i))
  filter_upwards [hcond, heq] with y hy hyEq
  intro i hi
  have hgne : g y ≠ 0 := by
    intro hz
    exact hi (by rw [hyEq i, hz, zero_mul])
  have hκne : condDistrib id obs μ y (E i) ≠ 0 := by
    intro hz
    exact hi (by rw [hyEq i, hz, mul_zero])
  exact hy hgne i hκne

/-- A finite-list refinement estimate with no measurability assumption on the
lists. Its loss is their pointwise size, rather than the total label count. -/
theorem observation_list_lowDensity_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    (obs : Ω → Y) (hobs : Measurable obs) (ρ : Measure Y) [SigmaFinite ρ]
    (g : Y → ENNReal) (hg : Measurable g) (hlaw : μ.map obs = ρ.withDensity g)
    (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (h : ι → Y → ENNReal) (hh : ∀ i, Measurable (h i))
    (hrestrict : ∀ i, (μ.restrict (E i)).map obs = ρ.withDensity (h i))
    (lst : Y → Finset ι) (hlist : ∀ i p, p ∈ E i → i ∈ lst (obs p))
    (ε K : ENNReal) (hK : ∀ y, ((lst y).card : ENNReal) ≤ K) :
    (∑ i, μ.restrict (E i) {p | h i (obs p) < ε * g (obs p)}) ≤
      ε * K * μ univ := by
  have hsupport := observation_list_density_support μ obs hobs ρ g hg hlaw E hE h hh
    hrestrict lst hlist
  have hlow : (∑ i, ∫⁻ y in Submission.Lib.K4Homogenization.lowDensity ε g (h i), h i y ∂ρ) ≤
      ε * K * ∫⁻ y, g y ∂ρ :=
    listed_lowDensity_mass ρ ε K g h hg hh (hsupport.mono fun y hy => ⟨lst y, hK y, hy⟩)
  have hmass : (∫⁻ y, g y ∂ρ) = μ univ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hlaw,
      Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
  rw [hmass] at hlow
  refine le_trans (le_of_eq ?_) hlow
  apply Finset.sum_congr rfl
  intro i _
  have hbad := Submission.Lib.K4Homogenization.measurableSet_lowDensity ε hg (hh i)
  change μ.restrict (E i) (obs ⁻¹' Submission.Lib.K4Homogenization.lowDensity ε g (h i)) = _
  rw [← Measure.map_apply hobs hbad, hrestrict i, withDensity_apply _ hbad]

end ObservationLists

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
