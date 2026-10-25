/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Profiles/DensityRefinement.lean. Earlier source attributions are retained below.
-/

/-
Adapted from this LOT tree, o006, session x0154, commit 1870328140507ff51223ba957b7b656e475b6f35,
Submission/Lib/K4DensityProfiles/DensityRefinement.lean.
The shared candidate has not been accepted into lib (capacity refusal).
-/

/-
Adapted from: here:o006
Original profile-selection bridge by session x0154.
-/

import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

/-!
# Refinement rates of logarithmic density profiles

The final inequality step in Lemma a01:homogenization. Monotonicity of densities
and the finite-refinement low-tail estimate force the limiting exponent to
increase by an amount between zero and the logarithmic refinement count.
-/

namespace Submission.Obl.k4_native_grid_profile_extension.Profiles

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- An inverse-subpower lower bound cannot itself be power-small. -/
theorem not_isPowerSmall_of_inverse_subpower {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) {a : ℕ → ℝ≥0∞}
    (ha : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ENNReal.ofReal (N k ^ (-ε)) ≤ a k) :
    ¬ IsPowerSmall N a := by
  rintro ⟨c, hc, hsmall⟩
  obtain ⟨k, hlow, hhigh, hNk⟩ := (ha (c / 2) (by positivity)).and
    (hsmall.and (hN.eventually (eventually_gt_atTop 1))) |>.exists
  have hstrict : ENNReal.ofReal (N k ^ (-c)) < ENNReal.ofReal (N k ^ (-(c / 2))) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos (by linarith) _)).mpr
    exact Real.rpow_lt_rpow_of_exponent_lt hNk (by linarith)
  exact not_le_of_gt hstrict (hlow.trans hhigh)

/-- A refinement with at most `N^(Δ+o(1))` choices has a power-small mass of entries
whose density loses more than `Δ+ε` powers relative to the old observation. -/
theorem refinement_tail_isPowerSmall {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (μ : (k : ℕ) → Measure (α k))
    (coarse fine : (k : ℕ) → α k → ℝ≥0∞) (Δ : ℝ) (D : ℕ → ℝ)
    (hD : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, D k ≤ N k ^ (Δ + ε))
    (htail : ∀ ε : ℝ, 0 < ε → ∀ k,
      μ k {x | fine k x < ENNReal.ofReal (N k ^ (-(Δ + ε))) * coarse k x} ≤
        ENNReal.ofReal (N k ^ (-(Δ + ε)) * D k)) :
    ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | fine k x < ENNReal.ofReal (N k ^ (-(Δ + ε))) * coarse k x}) := by
  intro ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  filter_upwards [hD (ε / 2) (by positivity)] with k hDk
  have hNk : 0 < N k := by linarith [hN k]
  refine (htail ε hε k).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    N k ^ (-(Δ + ε)) * D k ≤ N k ^ (-(Δ + ε)) * N k ^ (Δ + ε / 2) :=
      mul_le_mul_of_nonneg_left hDk (Real.rpow_nonneg hNk.le _)
    _ = N k ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hNk]
      congr 1
      ring

/-- A.e. refinement monotonicity forces the limiting exponent to increase, and
its low-tail bound controls the size of the increase. No common good point is
chosen across infinitely many depths or tolerances. -/
theorem density_exponent_increment_of_refinement {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (coarse fine : (k : ℕ) → α k → ℝ≥0∞) (e₀ e₁ Δ : ℝ)
    (hmass : ¬ IsPowerSmall N (fun k => μ k Set.univ))
    (hcoarse : HasTypicalDensity N μ coarse e₀)
    (hfine : HasTypicalDensity N μ fine e₁)
    (hmono : ∀ k, ∀ᵐ x ∂μ k, fine k x ≤ coarse k x)
    (htail : ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k =>
      μ k {x | fine k x < ENNReal.ofReal (N k ^ (-(Δ + ε))) * coarse k x})) :
    0 ≤ e₁ - e₀ ∧ e₁ - e₀ ≤ Δ := by
  constructor
  · by_contra! hneg
    let τ : ℝ := (e₀ - e₁) / 4
    have hτ : 0 < τ := by dsimp [τ]; linarith
    let C : (k : ℕ) → Set (α k) := fun k =>
      {x | coarse k x < ENNReal.ofReal (N k ^ (-e₀ - τ)) ∨
        ENNReal.ofReal (N k ^ (-e₀ + τ)) < coarse k x}
    let F : (k : ℕ) → Set (α k) := fun k =>
      {x | fine k x < ENNReal.ofReal (N k ^ (-e₁ - τ)) ∨
        ENNReal.ofReal (N k ^ (-e₁ + τ)) < fine k x}
    have hC : IsPowerSmall N (fun k => μ k (C k)) := hcoarse τ hτ
    have hF : IsPowerSmall N (fun k => μ k (F k)) := hfine τ hτ
    apply hmass ((hC.add hN hF).mono ?_)
    apply Eventually.of_forall
    intro k
    have hincl : ∀ᵐ x ∂μ k, x ∈ (Set.univ : Set (α k)) → x ∈ C k ∪ F k := by
      filter_upwards [hmono k] with x hx _
      by_cases hxC : x ∈ C k
      · exact Or.inl hxC
      by_cases hxF : x ∈ F k
      · exact Or.inr hxF
      simp only [C, F, mem_ofPred_eq, not_or, not_lt] at hxC hxF
      have hlt : ENNReal.ofReal (N k ^ (-e₀ + τ)) <
          ENNReal.ofReal (N k ^ (-e₁ - τ)) := by
        apply (ENNReal.ofReal_lt_ofReal_iff
          (Real.rpow_pos_of_pos (by linarith [hN₂ k]) _)).mpr
        apply Real.rpow_lt_rpow_of_exponent_lt (by linarith [hN₂ k])
        dsimp [τ]
        linarith
      exact (not_lt_of_ge (hxF.1.trans (hx.trans hxC.2)) hlt).elim
    exact (measure_mono_ae hincl).trans (measure_union_le _ _)
  · by_contra! hgap
    let τ : ℝ := (e₁ - e₀ - Δ) / 8
    have hτ : 0 < τ := by dsimp [τ]; linarith
    let C : (k : ℕ) → Set (α k) := fun k =>
      {x | coarse k x < ENNReal.ofReal (N k ^ (-e₀ - τ)) ∨
        ENNReal.ofReal (N k ^ (-e₀ + τ)) < coarse k x}
    let F : (k : ℕ) → Set (α k) := fun k =>
      {x | fine k x < ENNReal.ofReal (N k ^ (-e₁ - τ)) ∨
        ENNReal.ofReal (N k ^ (-e₁ + τ)) < fine k x}
    let T : (k : ℕ) → Set (α k) := fun k =>
      {x | fine k x < ENNReal.ofReal (N k ^ (-(Δ + 2 * τ))) * coarse k x}
    have hC : IsPowerSmall N (fun k => μ k (C k)) := hcoarse τ hτ
    have hF : IsPowerSmall N (fun k => μ k (F k)) := hfine τ hτ
    have hT : IsPowerSmall N (fun k => μ k (T k)) := htail (2 * τ) (by positivity)
    apply hmass (((hC.add hN hF).add hN hT).mono ?_)
    apply Eventually.of_forall
    intro k
    have hNk : 0 < N k := by linarith [hN₂ k]
    have hlt : ENNReal.ofReal (N k ^ (-e₁ + τ)) <
        ENNReal.ofReal (N k ^ (-(Δ + 2 * τ))) *
          ENNReal.ofReal (N k ^ (-e₀ - τ)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNk.le _), ← Real.rpow_add hNk]
      apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hNk _)).mpr
      apply Real.rpow_lt_rpow_of_exponent_lt (by linarith [hN₂ k])
      dsimp [τ]
      linarith
    have hincl : (Set.univ : Set (α k)) ⊆ (C k ∪ F k) ∪ T k := by
      intro x _
      by_cases hxC : x ∈ C k
      · exact Or.inl (Or.inl hxC)
      by_cases hxF : x ∈ F k
      · exact Or.inl (Or.inr hxF)
      simp only [C, F, mem_ofPred_eq, not_or, not_lt] at hxC hxF
      exact Or.inr ((hxF.2.trans_lt hlt).trans_le (mul_le_mul' le_rfl hxC.1))
    exact (measure_mono hincl).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))

end Submission.Obl.k4_native_grid_profile_extension.Profiles
