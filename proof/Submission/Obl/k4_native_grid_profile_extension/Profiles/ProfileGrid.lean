/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Profiles/ProfileGrid.lean. Earlier source attributions are retained below.
-/

/-
Adapted from this LOT tree, o006, session x0154, commit 1870328140507ff51223ba957b7b656e475b6f35,
Submission/Lib/K4DensityProfiles/ProfileGrid.lean.
The shared candidate has not been accepted into lib (capacity refusal).
-/

/-
Adapted from: here:o006
Original compact-depth grid extension by session x0154.
-/

import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

/-!
# Extending typical profiles on a closed depth interval

The depth interval in the exact-problem interface is compact. Adjoining constant
endpoint observations outside it reduces grid squeezing to the dense-grid theorem
on the real line, without requiring any observations beyond the given interval.
-/

namespace Submission.Obl.k4_native_grid_profile_extension.Profiles

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A grid dense in a closed interval becomes dense in the real line after
adjoining the two exterior tails. -/
theorem dense_interval_grid_with_tails {s : Set ℝ} {a b : ℝ}
    (hs : closure s = Icc a b) : Dense (s ∪ Iic a ∪ Ici b) := by
  rw [dense_iff_closure_eq, closure_union, closure_union, hs,
    isClosed_Iic.closure_eq, isClosed_Ici.closure_eq]
  ext x
  constructor
  · intro _
    trivial
  · intro _
    by_cases hxa : x ≤ a
    · exact Or.inl (Or.inr hxa)
    by_cases hbx : b ≤ x
    · exact Or.inr hbx
    exact Or.inl (Or.inl ⟨le_of_not_ge hxa, le_of_not_ge hbx⟩)

/-- Homogeneity on a grid containing the endpoints extends to the whole compact
depth interval when the observation densities are nested there. -/
theorem hasTypicalDensity_on_Icc_of_grid {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (g : ℝ → (k : ℕ) → α k → ℝ≥0∞) (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (grid : Set ℝ)
    (hgrid : closure grid = Icc a b) (ha : a ∈ grid) (hb : b ∈ grid)
    (htypical : ∀ r ∈ grid, HasTypicalDensity N μ (g r) (f r))
    (hmono : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s →
      ∀ k, ∀ᵐ x ∂μ k, g s k x ≤ g r k x) :
    ∀ r ∈ Icc a b, HasTypicalDensity N μ (g r) (f r) := by
  let clip : ℝ → ℝ := fun r => (projIcc a b hab r : ℝ)
  have hclip : Continuous clip := continuous_subtype_val.comp continuous_projIcc
  have hclipmono : Monotone clip := fun r s hrs => monotone_projIcc hab hrs
  have hclipmem (r : ℝ) : clip r ∈ Icc a b := (projIcc a b hab r).property
  have hclipself (r : ℝ) (hr : r ∈ Icc a b) : clip r = r :=
    congrArg Subtype.val (projIcc_of_mem hab hr)
  have hbase : ∀ r ∈ grid ∪ Iic a ∪ Ici b,
      HasTypicalDensity N μ (g (clip r)) (f (clip r)) := by
    intro r hr
    rcases hr with (hr | hr) | hr
    · have hr' : r ∈ Icc a b := hgrid ▸ subset_closure hr
      rw [hclipself r hr']
      exact htypical r hr
    · have hc : clip r = a := congrArg Subtype.val (projIcc_of_le_left hab hr)
      rw [hc]
      exact htypical a ha
    · have hc : clip r = b := congrArg Subtype.val (projIcc_of_right_le hab hr)
      rw [hc]
      exact htypical b hb
  have hall := hasTypicalDensity_of_dense_antitone N hN₁ hN μ
    (fun r => g (clip r)) (fun r => f (clip r)) (hf.comp hclip)
    (grid ∪ Iic a ∪ Ici b) (dense_interval_grid_with_tails hgrid) hbase
    (fun r s hrs => hmono (clip r) (hclipmem r) (clip s) (hclipmem s) (hclipmono hrs))
  intro r hr
  simpa only [hclipself r hr] using hall r

/-- Joint typical profiles extend from a product of compact depth grids to the
whole rectangle by applying the one-dimensional squeezing theorem twice. -/
theorem hasTypicalDensity_on_rectangle_of_grid {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (g : ℝ × ℝ → (k : ℕ) → α k → ℝ≥0∞) (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (gridR gridU : Set ℝ)
    (hgridR : closure gridR = Icc a b) (ha : a ∈ gridR) (hb : b ∈ gridR)
    (hgridU : closure gridU = Icc c d) (hc : c ∈ gridU) (hd : d ∈ gridU)
    (htypical : ∀ r ∈ gridR, ∀ u ∈ gridU, HasTypicalDensity N μ (g (r, u)) (f (r, u)))
    (hmonoR : ∀ u ∈ Icc c d, ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s →
      ∀ k, ∀ᵐ x ∂μ k, g (s, u) k x ≤ g (r, u) k x)
    (hmonoU : ∀ r ∈ Icc a b, ∀ u ∈ Icc c d, ∀ v ∈ Icc c d, u ≤ v →
      ∀ k, ∀ᵐ x ∂μ k, g (r, v) k x ≤ g (r, u) k x) :
    ∀ r ∈ Icc a b, ∀ u ∈ Icc c d, HasTypicalDensity N μ (g (r, u)) (f (r, u)) := by
  have hrows : ∀ u ∈ gridU, ∀ r ∈ Icc a b,
      HasTypicalDensity N μ (g (r, u)) (f (r, u)) := by
    intro u hu
    have hu' : u ∈ Icc c d := hgridU ▸ subset_closure hu
    exact hasTypicalDensity_on_Icc_of_grid N hN₁ hN μ (fun r => g (r, u))
      (fun r => f (r, u)) (hf.comp (continuous_id.prodMk continuous_const))
      hab gridR hgridR ha hb (fun r hr => htypical r hr u hu) (hmonoR u hu')
  intro r hr
  exact hasTypicalDensity_on_Icc_of_grid N hN₁ hN μ (fun u => g (r, u))
    (fun u => f (r, u)) (hf.comp (continuous_const.prodMk continuous_id))
    hcd gridU hgridU hc hd (fun u hu => hrows u hu r hr) (hmonoU r hr)

end Submission.Obl.k4_native_grid_profile_extension.Profiles
