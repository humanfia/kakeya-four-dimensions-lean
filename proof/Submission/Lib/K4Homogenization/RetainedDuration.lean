/-
Adapted from: here:o018
Written by x0048 in the o018 desk.
-/
import Mathlib

/-! Retained duration converts integrated incidence caps to fixed-time bounds for
an unchanged trajectory prior, as in paper Lemma a03:time-slice. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4Homogenization

noncomputable def incidenceDuration {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) (G : X × T → ℝ≥0∞) (I : Set T) (x : X) : ℝ≥0∞ :=
  ∫⁻ t in I, G (x, t) ∂τ

theorem measurable_incidenceDuration {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) [SFinite τ] {G : X × T → ℝ≥0∞} (hG : Measurable G) (I : Set T) :
    Measurable (incidenceDuration τ G I) := hG.lintegral_prod_right'

noncomputable def durationRetained {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) (G : X × T → ℝ≥0∞) (I : Set T) (a : ℝ≥0∞) : Set X :=
  {x | a ≤ incidenceDuration τ G I x}

theorem measurableSet_durationRetained {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (τ : Measure T) [SFinite τ] {G : X × T → ℝ≥0∞} (hG : Measurable G)
    (I : Set T) (a : ℝ≥0∞) : MeasurableSet (durationRetained τ G I a) :=
  measurableSet_le measurable_const (measurable_incidenceDuration τ hG I)

/-- The rectangle mass is the integral of original trajectory durations. -/
theorem duration_rectangle_mass {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G)
    {S : Set X} (hS : MeasurableSet S) {I : Set T} (hI : MeasurableSet I) :
    (ν.prod τ).withDensity G (S ×ˢ I) = ∫⁻ x in S, incidenceDuration τ G I x ∂ν := by
  rw [withDensity_apply _ (hS.prod hI), setLIntegral_prod _ hG.aemeasurable]
  rfl

/-- Omitting trajectories with short duration in one time window has cost at
most the threshold times the total original prior mass. -/
theorem duration_omission_mass_le {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G)
    {I : Set T} (hI : MeasurableSet I) (a : ℝ≥0∞) :
    (ν.prod τ).withDensity G ((durationRetained τ G I a)ᶜ ×ˢ I) ≤ a * ν univ := by
  have hL := measurableSet_durationRetained τ hG I a
  rw [duration_rectangle_mass ν τ hG hL.compl hI]
  calc
    _ ≤ ∫⁻ x in (durationRetained τ G I a)ᶜ, a ∂ν := by
      apply setLIntegral_mono measurable_const
      intro x hx
      exact le_of_lt (lt_of_not_ge hx)
    _ = a * ν (durationRetained τ G I a)ᶜ := by simp
    _ ≤ _ := mul_le_mul le_rfl (measure_mono (subset_univ _)) zero_le zero_le

/-- An integrated enlarged-constraint cap controls the original retained prior.
The constraint implication is required for every time in the same window. -/
theorem retained_duration_prior_cap {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G)
    {I : Set T} (hI : MeasurableSet I) (a : ℝ≥0∞)
    {C : Set X} (hC : MeasurableSet C) (Cplus : Set (X × T))
    (himp : ∀ x ∈ C, ∀ t ∈ I, (x, t) ∈ Cplus) :
    a * ν (durationRetained τ G I a ∩ C) ≤
      (ν.prod τ).withDensity G (Cplus ∩ (univ ×ˢ I)) := by
  have hL := measurableSet_durationRetained τ hG I a
  calc
    _ = ∫⁻ x in durationRetained τ G I a ∩ C, a ∂ν := by simp
    _ ≤ ∫⁻ x in durationRetained τ G I a ∩ C, incidenceDuration τ G I x ∂ν := by
      apply setLIntegral_mono (measurable_incidenceDuration τ hG I)
      intro x hx
      exact hx.1
    _ = (ν.prod τ).withDensity G ((durationRetained τ G I a ∩ C) ×ˢ I) :=
      (duration_rectangle_mass ν τ hG (hL.inter hC) hI).symm
    _ ≤ _ := measure_mono (by
      rintro ⟨x,t⟩ ⟨hx, ht⟩
      exact ⟨himp x hx.2 t ht, mem_univ _, ht⟩)

/-- The duration cut can be made separately on every member of a finite time
family. Only the sum of their time masses enters the deletion budget. -/
theorem duration_family_omission_mass_le {X T J : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [Fintype J]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G)
    (I : J → Set T) (hI : ∀ j, MeasurableSet (I j)) (ε : ℝ≥0∞) :
    (ν.prod τ).withDensity G
      (⋃ j, (durationRetained τ G (I j) (ε * τ (I j)))ᶜ ×ˢ I j) ≤
        (ε * ∑ j, τ (I j)) * ν univ := by
  calc
    _ ≤ ∑ j, (ν.prod τ).withDensity G
        ((durationRetained τ G (I j) (ε * τ (I j)))ᶜ ×ˢ I j) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ j, (ε * τ (I j)) * ν univ :=
      Finset.sum_le_sum (fun j _ => duration_omission_mass_le ν τ hG (hI j) _)
    _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]

/-- For a probability prior and time intervals of total length at most one,
duration pruning loses at most `ε` of the original incidence mass. -/
theorem duration_probability_omission_mass_le {X T J : Type*}
    [MeasurableSpace X] [MeasurableSpace T] [Fintype J]
    (ν : Measure X) [IsProbabilityMeasure ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G)
    (I : J → Set T) (hI : ∀ j, MeasurableSet (I j))
    (hsum : ∑ j, τ (I j) ≤ 1) (ε : ℝ≥0∞) :
    (ν.prod τ).withDensity G
      (⋃ j, (durationRetained τ G (I j) (ε * τ (I j)))ᶜ ×ˢ I j) ≤ ε := by
  calc
    _ ≤ (ε * ∑ j, τ (I j)) * ν univ := duration_family_omission_mass_le ν τ hG I hI ε
    _ ≤ (ε * 1) * 1 := by gcongr; simp
    _ = _ := by simp

/-- Division by a positive finite duration floor gives the usual fixed-time
prior cap. The right side still uses the original unnormalized incidence law. -/
theorem retained_duration_prior_cap_div {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G)
    {I : Set T} (hI : MeasurableSet I) (a : ℝ≥0∞) (ha0 : a ≠ 0) (hatop : a ≠ ∞)
    {C : Set X} (hC : MeasurableSet C) (Cplus : Set (X × T))
    (himp : ∀ x ∈ C, ∀ t ∈ I, (x, t) ∈ Cplus) :
    ν (durationRetained τ G I a ∩ C) ≤
      (ν.prod τ).withDensity G (Cplus ∩ (univ ×ˢ I)) / a := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hatop)).2
  rw [mul_comm]
  exact retained_duration_prior_cap ν τ hG hI a hC Cplus himp

/-- A product-a.e. incidence-density ceiling gives one a.e. time set on which
the entire instantaneous law is dominated by the unchanged trajectory prior. -/
theorem instantaneous_prior_domination {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G) (K : ℝ≥0∞)
    (hbound : ∀ᵐ p ∂ν.prod τ, G p ≤ K) :
    ∀ᵐ t ∂τ, ν.withDensity (fun x => G (x, t)) ≤ K • ν := by
  have hT : ∀ᵐ t ∂τ, ∀ᵐ x ∂ν, G (x, t) ≤ K :=
    (Measure.ae_ae_comm (μ := ν) (ν := τ) (p := fun x t => G (x, t) ≤ K)
      (measurableSet_le hG measurable_const)).mp
      (Measure.ae_ae_of_ae_prod hbound)
  filter_upwards [hT] with t ht
  simpa only [withDensity_const] using withDensity_mono ht

end Submission.Lib.K4Homogenization
