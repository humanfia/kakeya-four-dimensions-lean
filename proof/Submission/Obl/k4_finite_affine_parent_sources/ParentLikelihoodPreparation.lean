-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 37b81a6e.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ParentLikelihoodPreparation.lean.
-- Uses this obligation's checked nuE interface for the original conditional prior.
import Submission.Obl.k4_finite_affine_parent_sources.ModelMeasures

/-! Disintegrating a fixed original likelihood ceiling at one original
parent. Later submeasures retain the original parent's normalizing mass. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def fixedParentRestriction {Y : Type} [MeasurableSpace Y]
    (reference current : Measure Y) (S : Set Y) : Measure Y :=
  (reference S)⁻¹ • current.restrict S

theorem fixedParentRestriction_real {Y : Type} [MeasurableSpace Y]
    (reference current : Measure Y) (S A : Set Y) (hA : MeasurableSet A) :
    (fixedParentRestriction reference current S).real A =
      current.real (A ∩ S) / reference.real S := by
  rw [fixedParentRestriction, measureReal_ennreal_smul_apply, ENNReal.toReal_inv,
    measureReal_restrict_apply hA]
  change (reference.real S)⁻¹ * current.real (A ∩ S) = _
  ring

theorem fixedParentRestriction_self {Y : Type} [MeasurableSpace Y]
    (reference : Measure Y) (S : Set Y) :
    fixedParentRestriction reference reference S = nuE reference S := rfl

/-- The parent probability is conditioned from the original reference law.
The current incidence law is only scaled by that SAME original mass. The
global likelihood ceiling therefore gives a parentwise ceiling with the
actual original parent palette; no later success enters the denominator. -/
theorem likelihood_cap_in_original_parent
    {Y : Type} {H Z : Type*} [MeasurableSpace Y] [MeasurableSpace H]
    [MeasurableSingletonClass H] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (reference current : Measure Y) [IsFiniteMeasure reference]
    (fine coarse : Y → H) (parent : H → H) (palette : Y → Z)
    (hfine : Measurable fine) (_hcoarse : Measurable coarse) (hpalette : Measurable palette)
    (hrefine : ∀ y, coarse y = parent (fine y))
    (C : ℝ)
    (hcap : ∀ h z, current.real {y | (fine y, palette y) = (h, z)} ≤
      C * reference.real {y | fine y = h} *
        (reference.real {y | (coarse y, palette y) = (parent h, z)} /
          reference.real {y | coarse y = parent h}))
    (a : H) (ha : reference {y | coarse y = a} ≠ 0) :
    IsProbabilityMeasure (nuE reference {y | coarse y = a}) ∧
      ∀ h z,
        (fixedParentRestriction reference current {y | coarse y = a}).real
          {y | (fine y, palette y) = (h, z)} ≤
        C * (nuE reference {y | coarse y = a}).real {y | fine y = h} *
          (nuE reference {y | coarse y = a}).real {y | palette y = z} := by
  refine ⟨nuE_isProb reference _ ha (measure_ne_top _ _), ?_⟩
  intro h z
  have hF : MeasurableSet {y | fine y = h} := hfine (measurableSet_singleton h)
  have hZ : MeasurableSet {y | palette y = z} := hpalette (measurableSet_singleton z)
  have hJ : MeasurableSet {y | (fine y, palette y) = (h, z)} :=
    (hfine.prodMk hpalette) (measurableSet_singleton _)
  have hM : 0 < reference.real {y | coarse y = a} :=
    ENNReal.toReal_pos ha (measure_ne_top _ _)
  change (fixedParentRestriction reference current _).real _ ≤
    C * (fixedParentRestriction reference reference _).real _ *
      (fixedParentRestriction reference reference _).real _
  rw [fixedParentRestriction_real reference current _ _ hJ,
    fixedParentRestriction_real reference reference _ _ hF,
    fixedParentRestriction_real reference reference _ _ hZ]
  by_cases hh : parent h = a
  · have hFsub : {y | fine y = h} ⊆ {y | coarse y = a} := by
      intro y hy
      change coarse y = a
      rw [hrefine y, hy, hh]
    have hJsub : {y | (fine y, palette y) = (h, z)} ⊆ {y | coarse y = a} := by
      intro y hy
      exact hFsub (congrArg Prod.fst hy)
    rw [inter_eq_left.mpr hJsub, inter_eq_left.mpr hFsub]
    have hset : {y | palette y = z} ∩ {y | coarse y = a} =
        {y | (coarse y, palette y) = (a, z)} := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, Prod.mk.injEq, and_comm]
    rw [hset]
    have hc := hcap h z
    rw [hh] at hc
    have hd := div_le_div_of_nonneg_right hc hM.le
    convert hd using 1
    ring
  · have hzeroF : {y | fine y = h} ∩ {y | coarse y = a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hy, hc⟩
      exact hh (by rw [← hy, ← hrefine y]; exact hc)
    have hzeroJ : {y | (fine y, palette y) = (h, z)} ∩ {y | coarse y = a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hy, hc⟩
      have hf : fine y = h := congrArg Prod.fst hy
      exact hh (by rw [← hf, ← hrefine y]; exact hc)
    rw [hzeroJ, hzeroF, measureReal_empty, measureReal_empty, zero_div, mul_zero, zero_mul]

end

end Submission.Obl.k4_finite_affine_parent_sources
