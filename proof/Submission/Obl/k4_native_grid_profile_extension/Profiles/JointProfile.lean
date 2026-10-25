/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Profiles/JointProfile.lean. Earlier source attributions are retained below.
-/

/-
Adapted from this LOT tree, o006, session x0154, commit 1870328140507ff51223ba957b7b656e475b6f35,
Submission/Lib/K4DensityProfiles/JointProfile.lean.
The shared candidate has not been accepted into lib (capacity refusal).
-/

/-
Adapted from: here:o006
Own-tree profile and density-selection helpers, sessions x0154 and x0006.
The slow finite-requirement diagonal was originally written by x0006 (1fa80d3).
-/

import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileCompactness

/-!
# Joint hidden-depth and angular-depth profiles

The second part of the profile compactness step in Lemma a01:homogenization.
An asymmetric continuous increment bound survives extension from a countable grid.
For the hidden and angular depths its cost is the sum of the positive coordinate
increments, with angular coefficient equal to the velocity dimension.
-/

namespace Submission.Obl.k4_native_grid_profile_extension.Profiles

open Set Filter
open scoped Topology NNReal

/-- Extend a grid function while retaining a continuous asymmetric increment cost.
The cost is bounded above by a multiple of the ambient metric. -/
theorem extend_profile_with_cost {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (a : s → ℝ) (cost : X × X → ℝ) (K : ℝ≥0)
    (hc : Continuous cost)
    (hcost : ∀ x y, cost (x, y) ≤ (K : ℝ) * dist x y)
    (hinc : ∀ x y : s, a y - a x ≤ cost (x, y)) :
    ∃ f : X → ℝ, LipschitzWith K f ∧ (∀ x : s, f x = a x) ∧
      ∀ x ∈ closure s, ∀ y ∈ closure s, f y - f x ≤ cost (x, y) := by
  classical
  let a₀ : X → ℝ := fun x => if hx : x ∈ s then a ⟨x, hx⟩ else 0
  have ha₀ (x : s) : a₀ x = a x := by simp [a₀]
  have hlip : LipschitzOnWith K a₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq]
    simp only [a₀, dite_eq_left hx, dite_eq_left hy]
    apply abs_le.mpr
    have h₁ := (hinc ⟨x, hx⟩ ⟨y, hy⟩).trans (hcost x y)
    have h₂ := (hinc ⟨y, hy⟩ ⟨x, hx⟩).trans (hcost y x)
    rw [dist_comm y x] at h₂
    constructor <;> linarith
  obtain ⟨f, hf, hfa⟩ := hlip.extend_real
  have hfa' (x : s) : f x = a x := (hfa x.property).symm.trans (ha₀ x)
  have hdir : ∀ p ∈ s ×ˢ s, f p.2 - f p.1 ≤ cost p := by
    intro p hp
    have h₁ := hfa' ⟨p.1, hp.1⟩
    have h₂ := hfa' ⟨p.2, hp.2⟩
    dsimp only at h₁ h₂
    rw [h₁, h₂]
    exact hinc ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩
  refine ⟨f, hf, hfa', ?_⟩
  intro x hx y hy
  exact le_on_closure (x := (x, y)) hdir
    ((hf.continuous.comp continuous_snd).sub
      (hf.continuous.comp continuous_fst)).continuousOn hc.continuousOn
    (by simpa only [closure_prod_eq, mem_prod] using And.intro hx hy)

/-- Bounded logarithmic arrays with asymptotic increment estimates produce a
continuous profile satisfying those estimates exactly on the grid closure. -/
theorem exists_density_profile_with_cost {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : s.Countable) (a : ℕ → s → ℝ) (lo hi : ℝ)
    (ha : ∀ k x, a k x ∈ Icc lo hi)
    (cost : X × X → ℝ) (K : ℝ≥0) (hc : Continuous cost)
    (hcost : ∀ x y, cost (x, y) ≤ (K : ℝ) * dist x y)
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hinc : ∀ x y : s, ∀ᶠ k in atTop,
      a k y - a k x ≤ cost (x, y) + err k) :
    ∃ (φ : ℕ → ℕ) (f : X → ℝ), StrictMono φ ∧ LipschitzWith K f ∧
      (∀ x ∈ closure s, f x ∈ Icc lo hi) ∧
      (∀ x ∈ closure s, ∀ y ∈ closure s, f y - f x ≤ cost (x, y)) ∧
      ∀ x : s, Tendsto (fun k => a (φ k) x) atTop (𝓝 (f x)) := by
  let : Countable s := hs
  obtain ⟨φ, g, hφ, hg, hlim⟩ :=
    countable_bounded_subsequence a (fun _ => lo) (fun _ => hi) ha
  have hgrid (x y : s) : g y - g x ≤ cost (x, y) := by
    have h := le_of_tendsto_of_tendsto ((hlim y).sub (hlim x))
      (tendsto_const_nhds.add (herr.comp hφ.tendsto_atTop))
      (hφ.tendsto_atTop.eventually (hinc x y))
    simpa only [Function.comp_apply, add_zero] using h
  obtain ⟨f, hf, hfg, hprofile⟩ := extend_profile_with_cost g cost K hc hcost hgrid
  refine ⟨φ, f, hφ, hf, ?_, hprofile, ?_⟩
  · have hc' : IsClosed (f ⁻¹' Icc lo hi) := isClosed_Icc.preimage hf.continuous
    apply closure_minimal ?_ hc'
    intro x hx
    simpa only [mem_preimage, hfg ⟨x, hx⟩] using hg ⟨x, hx⟩
  · intro x
    simpa only [hfg] using hlim x

/-- The increment cost of one hidden coordinate and `j` velocity coordinates. -/
def jointProfileCost (j : ℝ) (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  max 0 (p.2.1 - p.1.1) + j * max 0 (p.2.2 - p.1.2)

theorem continuous_jointProfileCost (j : ℝ) : Continuous (jointProfileCost j) :=
  (continuous_const.max (continuous_snd.fst.sub continuous_fst.fst)).add
    ((continuous_const.max (continuous_snd.snd.sub continuous_fst.snd)).const_mul j)

theorem jointProfileCost_le_dist {j : ℝ} (hj : 0 ≤ j) (x y : ℝ × ℝ) :
    jointProfileCost j (x, y) ≤ (1 + j) * dist x y := by
  have h₁ : max 0 (y.1 - x.1) ≤ dist x y := by
    apply max_le dist_nonneg
    exact (le_abs_self _).trans (by simpa [Real.dist_eq, abs_sub_comm] using (show dist x.1 y.1 ≤ dist x y by rw [Prod.dist_eq]; exact le_max_left _ _))
  have h₂ : max 0 (y.2 - x.2) ≤ dist x y := by
    apply max_le dist_nonneg
    exact (le_abs_self _).trans (by simpa [Real.dist_eq, abs_sub_comm] using (show dist x.2 y.2 ≤ dist x y by rw [Prod.dist_eq]; exact le_max_right _ _))
  dsimp [jointProfileCost]
  nlinarith [mul_le_mul_of_nonneg_left h₂ hj]

/-- The joint grid profile has Lipschitz constants one in hidden depth and `j`
in angular depth; a single convergent subsequence supplies both. -/
theorem exists_joint_density_profile {s : Set (ℝ × ℝ)} (hs : s.Countable)
    (j : ℝ≥0) (a : ℕ → s → ℝ) (lo hi : ℝ)
    (ha : ∀ k x, a k x ∈ Icc lo hi)
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hinc : ∀ x y : s, ∀ᶠ k in atTop,
      a k y - a k x ≤ jointProfileCost j (x, y) + err k) :
    ∃ (φ : ℕ → ℕ) (f : ℝ × ℝ → ℝ), StrictMono φ ∧ LipschitzWith (1 + j) f ∧
      (∀ x ∈ closure s, f x ∈ Icc lo hi) ∧
      (∀ x ∈ closure s, ∀ y ∈ closure s,
        f y - f x ≤ jointProfileCost j (x, y)) ∧
      ∀ x : s, Tendsto (fun k => a (φ k) x) atTop (𝓝 (f x)) := by
  apply exists_density_profile_with_cost hs a lo hi ha (jointProfileCost j) (1 + j)
    (continuous_jointProfileCost j) ?_ err herr hinc
  intro x y
  simpa only [NNReal.coe_add, NNReal.coe_one] using jointProfileCost_le_dist j.coe_nonneg x y

/-- The asymmetric joint bound yields the separate monotonicity and refinement
rates in the statement of the homogenization lemma. -/
theorem joint_profile_coordinate_increments {s : Set (ℝ × ℝ)} {j : ℝ}
    {f : ℝ × ℝ → ℝ}
    (hf : ∀ x ∈ s, ∀ y ∈ s, f y - f x ≤ jointProfileCost j (x, y)) :
    (∀ r r' u : ℝ, (r, u) ∈ s → (r', u) ∈ s → r ≤ r' →
      0 ≤ f (r', u) - f (r, u) ∧ f (r', u) - f (r, u) ≤ r' - r) ∧
    (∀ r u u' : ℝ, (r, u) ∈ s → (r, u') ∈ s → u ≤ u' →
      0 ≤ f (r, u') - f (r, u) ∧ f (r, u') - f (r, u) ≤ j * (u' - u)) := by
  constructor
  · intro r r' u hr hr' hrr
    have h₁ := hf (r, u) hr (r', u) hr'
    have h₂ := hf (r', u) hr' (r, u) hr
    simp only [jointProfileCost, sub_self, max_self, mul_zero, add_zero,
      max_eq_right (sub_nonneg.mpr hrr), max_eq_left (sub_nonpos.mpr hrr)] at h₁ h₂
    constructor <;> linarith
  · intro r u u' hu hu' huu
    have h₁ := hf (r, u) hu (r, u') hu'
    have h₂ := hf (r, u') hu' (r, u) hu
    simp only [jointProfileCost, sub_self, max_self, mul_zero, zero_add,
      max_eq_right (sub_nonneg.mpr huu), max_eq_left (sub_nonpos.mpr huu)] at h₁ h₂
    constructor <;> linarith

end Submission.Obl.k4_native_grid_profile_extension.Profiles
