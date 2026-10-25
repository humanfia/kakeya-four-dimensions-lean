/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Profiles/ProfileCompactness.lean. Earlier source attributions are retained below.
-/

/-
Adapted from this LOT tree, o006, session x0154, commit 1870328140507ff51223ba957b7b656e475b6f35,
Submission/Lib/K4DensityProfiles/ProfileCompactness.lean.
The shared candidate has not been accepted into lib (capacity refusal).
-/

/-
Adapted from: here:o006
Own-tree profile and density-selection helpers, sessions x0154 and x0006.
The slow finite-requirement diagonal was originally written by x0006 (1fa80d3).
-/

import Mathlib

/-!
# Limits of logarithmic density profiles

The compactness and extension step in Lemma a01:homogenization of the supplied
paper. The measure-theoretic selections supplying the grid exponents are separate:
bounded exponents on a countable depth grid admit a common convergent subsequence;
asymptotic refinement inequalities give a monotone, one-Lipschitz limiting profile.
-/

namespace Submission.Obl.k4_native_grid_profile_extension.Profiles

open Set Filter
open scoped Topology

/-- Bounded real arrays with countably many columns have a subsequence converging
in every column at once. The bounds may depend on the column. -/
theorem countable_bounded_subsequence {ι : Type*} [Countable ι]
    (a : ℕ → ι → ℝ) (lo hi : ι → ℝ)
    (ha : ∀ k i, a k i ∈ Icc (lo i) (hi i)) :
    ∃ (φ : ℕ → ℕ) (g : ι → ℝ), StrictMono φ ∧
      (∀ i, g i ∈ Icc (lo i) (hi i)) ∧
      ∀ i, Tendsto (fun k => a (φ k) i) atTop (𝓝 (g i)) := by
  have hc : IsCompact (Set.univ.pi (fun i => Icc (lo i) (hi i))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hc.tendsto_subseq (x := a)
    (fun k i _ => ha k i)
  exact ⟨φ, g, hφ, fun i => hg i (mem_univ i), fun i => hlim.apply_nhds i⟩

/-- Refinement inequalities with an error tending to zero become exact along a
pointwise convergent subsequence. -/
theorem profile_increment_of_tendsto {ι : Type*} (depth : ι → ℝ)
    (a : ℕ → ι → ℝ) (g : ι → ℝ) (err : ℕ → ℝ)
    (hlim : ∀ i, Tendsto (fun k => a k i) atTop (𝓝 (g i)))
    (herr : Tendsto err atTop (𝓝 0))
    (hinc : ∀ i j, depth i ≤ depth j → ∀ᶠ k in atTop,
      -err k ≤ a k j - a k i ∧
        a k j - a k i ≤ depth j - depth i + err k) :
    ∀ i j, depth i ≤ depth j →
      0 ≤ g j - g i ∧ g j - g i ≤ depth j - depth i := by
  intro i j hij
  have hd := (hlim j).sub (hlim i)
  have hp := hinc i j hij
  constructor
  · have h := le_of_tendsto_of_tendsto herr.neg hd (hp.mono fun _ h => h.1)
    simpa only [neg_zero] using h
  · have h := le_of_tendsto_of_tendsto hd
      (tendsto_const_nhds.add herr) (hp.mono fun _ h => h.2)
    simpa only [add_zero] using h

/-- A monotone one-Lipschitz function on a depth grid extends to its closure,
with the same increment inequalities. -/
theorem extend_profile_from_grid {s : Set ℝ} (a : s → ℝ)
    (hinc : ∀ x y : s, (x : ℝ) ≤ y →
      0 ≤ a y - a x ∧ a y - a x ≤ (y : ℝ) - x) :
    ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧
      (∀ x : s, f x = a x) ∧
      ∀ x ∈ closure s, ∀ y ∈ closure s, x ≤ y →
        0 ≤ f y - f x ∧ f y - f x ≤ y - x := by
  classical
  let a₀ : ℝ → ℝ := fun x => if hx : x ∈ s then a ⟨x, hx⟩ else 0
  have ha₀ (x : s) : a₀ x = a x := by simp [a₀]
  have hdir (x y : s) : a x ≤ a y + max 0 ((x : ℝ) - y) := by
    rcases le_total (x : ℝ) y with hxy | hyx
    · have h := (hinc x y hxy).1
      rw [max_eq_left (sub_nonpos.mpr hxy)]
      linarith
    · have h := (hinc y x hyx).2
      rw [max_eq_right (sub_nonneg.mpr hyx)]
      linarith
  have hlip : LipschitzOnWith 1 a₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    have hxy := hdir ⟨x, hx⟩ ⟨y, hy⟩
    have hyx := hdir ⟨y, hy⟩ ⟨x, hx⟩
    simp only [a₀, dite_eq_left hx, dite_eq_left hy]
    apply abs_le.mpr
    constructor
    · have hm : max 0 (y - x) ≤ |x - y| := by
        rw [abs_sub_comm x y]
        exact max_le (abs_nonneg _) (le_abs_self _)
      linarith
    · have hm : max 0 (x - y) ≤ |x - y| :=
        max_le (abs_nonneg _) (le_abs_self _)
      linarith
  obtain ⟨f, hf, hfa⟩ := hlip.extend_real
  have hfa' (x : s) : f x = a x := (hfa x.property).symm.trans (ha₀ x)
  have hdir' : ∀ p ∈ s ×ˢ s, f p.1 ≤ f p.2 + max 0 (p.1 - p.2) := by
    intro p hp
    have h₁ := hfa' ⟨p.1, hp.1⟩
    have h₂ := hfa' ⟨p.2, hp.2⟩
    dsimp only at h₁ h₂
    rw [h₁, h₂]
    exact hdir ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩
  have hclosed (x y : ℝ) (hx : x ∈ closure s) (hy : y ∈ closure s) :
      f x ≤ f y + max 0 (x - y) := by
    exact le_on_closure (x := (x, y)) hdir'
      (hf.continuous.comp continuous_fst).continuousOn
      ((hf.continuous.comp continuous_snd).add
        (continuous_const.max (continuous_fst.sub continuous_snd))).continuousOn
      (by simpa only [closure_prod_eq, mem_prod] using And.intro hx hy)
  refine ⟨f, hf, hfa', ?_⟩
  intro x hx y hy hxy
  have h₁ := hclosed x y hx hy
  have h₂ := hclosed y x hy hx
  rw [max_eq_left (sub_nonpos.mpr hxy)] at h₁
  rw [max_eq_right (sub_nonneg.mpr hxy)] at h₂
  constructor <;> linarith

/-- Simultaneous subsequence extraction and extension for a countable depth grid.
This is the compactness part of the homogeneous-profile construction. -/
theorem exists_density_profile {s : Set ℝ} (hs : s.Countable)
    (a : ℕ → s → ℝ) (lo hi : ℝ)
    (ha : ∀ k x, a k x ∈ Icc lo hi)
    (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (hinc : ∀ x y : s, (x : ℝ) ≤ y → ∀ᶠ k in atTop,
      -err k ≤ a k y - a k x ∧
        a k y - a k x ≤ (y : ℝ) - x + err k) :
    ∃ (φ : ℕ → ℕ) (f : ℝ → ℝ), StrictMono φ ∧ LipschitzWith 1 f ∧
      (∀ x ∈ closure s, f x ∈ Icc lo hi) ∧
      (∀ x ∈ closure s, ∀ y ∈ closure s, x ≤ y →
        0 ≤ f y - f x ∧ f y - f x ≤ y - x) ∧
      ∀ x : s, Tendsto (fun k => a (φ k) x) atTop (𝓝 (f x)) := by
  let : Countable s := hs
  obtain ⟨φ, g, hφ, hg, hlim⟩ :=
    countable_bounded_subsequence a (fun _ => lo) (fun _ => hi) ha
  have hgrid : ∀ x y : s, (x : ℝ) ≤ y →
      0 ≤ g y - g x ∧ g y - g x ≤ (y : ℝ) - x := by
    apply profile_increment_of_tendsto (fun x : s => (x : ℝ))
      (fun k => a (φ k)) g (err ∘ φ) hlim (herr.comp hφ.tendsto_atTop)
    intro x y hxy
    exact hφ.tendsto_atTop.eventually (hinc x y hxy)
  obtain ⟨f, hf, hfg, hprofile⟩ := extend_profile_from_grid g hgrid
  refine ⟨φ, f, hφ, hf, ?_, hprofile, ?_⟩
  · have hc : IsClosed (f ⁻¹' Icc lo hi) := isClosed_Icc.preimage hf.continuous
    apply closure_minimal ?_ hc
    intro x hx
    simpa only [mem_preimage, hfg ⟨x, hx⟩] using hg ⟨x, hx⟩
  · intro x
    simpa only [hfg] using hlim x

end Submission.Obl.k4_native_grid_profile_extension.Profiles
