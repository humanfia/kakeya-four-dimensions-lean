/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/GridExtension.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.NativeIncrements
import Submission.Obl.k4_native_grid_profile_extension.DepthGrid
import Submission.Obl.k4_native_grid_profile_extension.Profiles.JointProfile

/-!
# Extend a typical native grid profile to a depth rectangle
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- Native typicality on a dense product grid determines a continuous joint profile
with the sharp separate increment bounds, and gives typicality at every depth. -/
theorem extend_native_typical_grid
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : ℕ → Measure (Coefficients × ℝ)) [∀ k, IsFiniteMeasure (μ k)]
    (hmass : ∀ k, μ k Set.univ ≤ 1)
    (hnonzero : ¬ Profiles.IsPowerSmall N (fun k => μ k Set.univ))
    {R U : ℝ} (hR : 0 < R) (hU : 0 < U) (hExists : DensityExists N μ R U)
    (a : (depthGrid R ×ˢ depthGrid U) → ℝ)
    (htypical : ∀ x : depthGrid R ×ˢ depthGrid U,
      Profiles.HasTypicalDensity N μ (nativeDensityAt N μ x.1.1 x.1.2) (a x)) :
    ∃ F : ℝ → ℝ → ℝ, ProfileRegular R U F ∧
      ∀ r ∈ Icc (0 : ℝ) R, ∀ u ∈ Icc (0 : ℝ) U,
        Profiles.HasTypicalDensity N μ (nativeDensityAt N μ r u) (F r u) := by
  classical
  let grid := depthGrid R ×ˢ depthGrid U
  have hrange : ∀ x : grid, x.1 ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) U := by
    intro x
    constructor
    · rw [← closure_depthGrid hR.le]
      exact subset_closure x.2.1
    · rw [← closure_depthGrid hU.le]
      exact subset_closure x.2.2
  have hincrement (x y : grid) (hr : x.1.1 ≤ y.1.1) (hu : x.1.2 ≤ y.1.2) :
      0 ≤ a y - a x ∧ a y - a x ≤ (y.1.1 - x.1.1) + 2 * (y.1.2 - x.1.2) :=
    native_density_exponent_increment N hN₂ hN μ hmass hnonzero hExists
      (hrange x).1.1 hr (hrange y).1.2 (hrange x).2.1 hu (hrange y).2.2
      (htypical x) (htypical y)
  have hcost : ∀ x y : grid, a y - a x ≤ Profiles.jointProfileCost 2 (x, y) := by
    intro x y
    have hzR : max x.1.1 y.1.1 ∈ depthGrid R := by
      by_cases h : x.1.1 ≤ y.1.1
      · simpa only [max_eq_right h] using y.2.1
      · simpa only [max_eq_left (le_of_not_ge h)] using x.2.1
    have hzU : max x.1.2 y.1.2 ∈ depthGrid U := by
      by_cases h : x.1.2 ≤ y.1.2
      · simpa only [max_eq_right h] using y.2.2
      · simpa only [max_eq_left (le_of_not_ge h)] using x.2.2
    let z : grid := ⟨(max x.1.1 y.1.1, max x.1.2 y.1.2), hzR, hzU⟩
    have hxz := hincrement x z (le_max_left _ _) (le_max_left _ _)
    have hyz := hincrement y z (le_max_right _ _) (le_max_right _ _)
    have hmax (b c : ℝ) : max b c - b = max 0 (c - b) := by
      by_cases h : b ≤ c
      · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
      · rw [max_eq_left (le_of_not_ge h), sub_self,
          max_eq_left (sub_nonpos.mpr (le_of_not_ge h))]
    have hdiff : (z.1.1 - x.1.1) + 2 * (z.1.2 - x.1.2) =
        Profiles.jointProfileCost 2 (x, y) := by
      change (max x.1.1 y.1.1 - x.1.1) + 2 * (max x.1.2 y.1.2 - x.1.2) = _
      rw [hmax, hmax]
      rfl
    calc
      a y - a x ≤ a z - a x := by linarith [hyz.1]
      _ ≤ Profiles.jointProfileCost 2 (x, y) := hxz.2.trans_eq hdiff
  obtain ⟨f, hf, hfa, hinc⟩ := Profiles.extend_profile_with_cost a
    (Profiles.jointProfileCost 2) 3 (Profiles.continuous_jointProfileCost 2)
    (by
      intro x y
      convert Profiles.jointProfileCost_le_dist (j := 2) (by norm_num) x y using 1 <;>
        norm_num)
    hcost
  have hclosure : closure (depthGrid R ×ˢ depthGrid U) =
      Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) U := by
    rw [closure_prod_eq, closure_depthGrid hR.le, closure_depthGrid hU.le]
  have hinc' : ∀ x ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) U,
      ∀ y ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) U,
        f y - f x ≤ Profiles.jointProfileCost 2 (x, y) := by
    simpa only [hclosure] using hinc
  have hcoords := Profiles.joint_profile_coordinate_increments hinc'
  refine ⟨(fun r u => f (r, u)), ⟨?_, ?_⟩, ?_⟩
  · intro r s u hr hrs hsR hu huU
    exact hcoords.1 r s u ⟨⟨hr, hrs.trans hsR⟩, hu, huU⟩
      ⟨⟨hr.trans hrs, hsR⟩, hu, huU⟩ hrs
  · intro r u v hr hrR hu huv hvU
    exact hcoords.2 r u v ⟨⟨hr, hrR⟩, hu, huv.trans hvU⟩
      ⟨⟨hr, hrR⟩, hu.trans huv, hvU⟩ huv
  · apply Profiles.hasTypicalDensity_on_rectangle_of_grid N
      (fun k => by linarith [hN₂ k]) hN μ
      (fun p => nativeDensityAt N μ p.1 p.2) f hf.continuous hR.le hU.le
      (depthGrid R) (depthGrid U) (closure_depthGrid hR.le)
      (zero_mem_depthGrid hR.le) (right_mem_depthGrid hR.le)
      (closure_depthGrid hU.le) (zero_mem_depthGrid hU.le) (right_mem_depthGrid hU.le)
    · intro r hr u hu
      have hx := htypical (⟨(r, u), hr, hu⟩ : grid)
      simpa only [hfa (⟨(r, u), hr, hu⟩ : grid)] using hx
    · intro u hu r hr s hs hrs k
      exact native_refinement_density_le (μ k) (by linarith [hN₂ k])
        hr.1 hrs hu.1 le_rfl _ _ (measurable_nativeDensity _ _ _ _)
        (measurable_nativeDensity _ _ _ _)
        (nativeDensity_law (μ k) (N k) r u (hExists k r u hr.1 hr.2 hu.1 hu.2))
        (nativeDensity_law (μ k) (N k) s u (hExists k s u hs.1 hs.2 hu.1 hu.2))
    · intro r hr u hu v hv huv k
      exact native_refinement_density_le (μ k) (by linarith [hN₂ k])
        hr.1 le_rfl hu.1 huv _ _ (measurable_nativeDensity _ _ _ _)
        (measurable_nativeDensity _ _ _ _)
        (nativeDensity_law (μ k) (N k) r u (hExists k r u hr.1 hr.2 hu.1 hu.2))
        (nativeDensity_law (μ k) (N k) r v (hExists k r v hr.1 hr.2 hv.1 hv.2))

end Submission.Obl.k4_native_grid_profile_extension
