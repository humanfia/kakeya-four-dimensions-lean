/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Profiles/TypicalDensity.lean. Earlier source attributions are retained below.
-/

/-
Adapted from this LOT tree, o006, session x0154, commit 1870328140507ff51223ba957b7b656e475b6f35,
Submission/Lib/K4DensityProfiles/TypicalDensity.lean.
The shared candidate has not been accepted into lib (capacity refusal).
-/

/-
Adapted from: here:o006
Own-tree profile and density-selection helpers, sessions x0154 and x0006.
The slow finite-requirement diagonal was originally written by x0006 (1fa80d3).
-/

import Mathlib

/-!
# Typical densities under restriction and normalization

The comparison step in Lemmas a01:density-operations and a01:homogenization.
The underlying restriction estimate is an input here; this module converts it,
uniform bounds for the old density, and subpower normalization losses into the
power-small exceptional sets required by the exact-problem interface.
-/

namespace Submission.Obl.k4_native_grid_profile_extension.Profiles

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A varying nonnegative quantity is bounded by a fixed negative power,
eventually. -/
def IsPowerSmall (N : ℕ → ℝ) (a : ℕ → ℝ≥0∞) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, a k ≤ ENNReal.ofReal (N k ^ (-c))

theorem IsPowerSmall.mono {N : ℕ → ℝ} {a b : ℕ → ℝ≥0∞}
    (ha : IsPowerSmall N a) (hba : ∀ᶠ k in atTop, b k ≤ a k) : IsPowerSmall N b := by
  obtain ⟨c, hc, hbound⟩ := ha
  exact ⟨c, hc, (hba.and hbound).mono fun _ h => h.1.trans h.2⟩

/-- Adding finitely many power-small exceptional masses still gives a power-small
exceptional mass. -/
theorem IsPowerSmall.add {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {a b : ℕ → ℝ≥0∞} (ha : IsPowerSmall N a) (hb : IsPowerSmall N b) :
    IsPowerSmall N (fun k => a k + b k) := by
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  let e : ℝ := min c d
  have he : 0 < e := lt_min hc hd
  have hetop : ∀ᶠ k in atTop, 2 ≤ N k ^ (e / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < e / 2)).comp hN).eventually
      (eventually_ge_atTop 2)
  refine ⟨e / 2, by positivity, ?_⟩
  filter_upwards [ha, hb, hetop, hN.eventually (eventually_ge_atTop 1)]
    with k hak hbk he₂ hNk
  have hNpos : 0 < N k := by linarith
  have hc' : N k ^ (-c) ≤ N k ^ (-e) :=
    Real.rpow_le_rpow_of_exponent_le hNk (neg_le_neg (min_le_left _ _))
  have hd' : N k ^ (-d) ≤ N k ^ (-e) :=
    Real.rpow_le_rpow_of_exponent_le hNk (neg_le_neg (min_le_right _ _))
  calc
    a k + b k ≤ ENNReal.ofReal (N k ^ (-e)) + ENNReal.ofReal (N k ^ (-e)) :=
      add_le_add (hak.trans (ENNReal.ofReal_le_ofReal hc'))
        (hbk.trans (ENNReal.ofReal_le_ofReal hd'))
    _ = ENNReal.ofReal (2 * N k ^ (-e)) := by
      rw [two_mul, ENNReal.ofReal_add (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)]
    _ ≤ ENNReal.ofReal (N k ^ (-(e / 2))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        2 * N k ^ (-e) ≤ N k ^ (e / 2) * N k ^ (-e) :=
          mul_le_mul_of_nonneg_right he₂ (Real.rpow_nonneg hNpos.le _)
        _ = N k ^ (-(e / 2)) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring

/-- A density has a fixed logarithmic exponent outside a power-small exceptional
set, for every fixed positive tolerance. Measures and state spaces may vary. -/
def HasTypicalDensity {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (μ : (k : ℕ) → Measure (α k))
    (g : (k : ℕ) → α k → ℝ≥0∞) (e : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
    μ k {x | g k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
      ENNReal.ofReal (N k ^ (-e + τ)) < g k x} ≤ ENNReal.ofReal (N k ^ (-c))

/-- A fixed exponent for the old density persists for the current density when
small relative densities have the restriction bound and normalization is subpower.
This also allows the upper bound to grow by that normalization factor. -/
theorem hasTypicalDensity_of_comparison {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (μ : (k : ℕ) → Measure (α k))
    (old current : (k : ℕ) → α k → ℝ≥0∞) (e : ℝ)
    (K : ℕ → ℝ)
    (hK : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (hold : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k,
      ENNReal.ofReal (N k ^ (-e - ε)) ≤ old k x ∧
        old k x ≤ ENNReal.ofReal (N k ^ (-e + ε)))
    (hupper : ∀ k, ∀ᵐ x ∂μ k, current k x ≤ ENNReal.ofReal (K k) * old k x)
    (hdrop : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      μ k {x | current k x < ENNReal.ofReal (N k ^ (-ε)) * old k x} ≤
        ENNReal.ofReal (N k ^ (-ε) * K k)) :
    HasTypicalDensity N μ current e := by
  intro τ hτ
  have hτ₃ : 0 < τ / 3 := by positivity
  have hτ₆ : 0 < τ / 6 := by positivity
  refine ⟨τ / 6, hτ₆, ?_⟩
  filter_upwards [hold (τ / 3) hτ₃, hK (τ / 3) hτ₃, hK (τ / 6) hτ₆,
    hdrop (τ / 3) hτ₃] with k holdk hK₃ hK₆ hdropk
  have hNk : 0 < N k := by linarith [hN k]
  have hlow : ENNReal.ofReal (N k ^ (-e - τ)) ≤
      ENNReal.ofReal (N k ^ (-(τ / 3))) * ENNReal.ofReal (N k ^ (-e - τ / 3)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNk.le _), ← Real.rpow_add hNk]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith))
  have hhigh : ENNReal.ofReal (N k ^ (τ / 3)) * ENNReal.ofReal (N k ^ (-e + τ / 3)) ≤
      ENNReal.ofReal (N k ^ (-e + τ)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNk.le _), ← Real.rpow_add hNk]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (hN k) (by linarith))
  have hincl : ∀ᵐ x ∂μ k,
      (current k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < current k x) →
      current k x < ENNReal.ofReal (N k ^ (-(τ / 3))) * old k x := by
    filter_upwards [holdk, hupper k] with x hx hcur hbad
    rcases hbad with hbad | hbad
    · exact hbad.trans_le (hlow.trans (mul_le_mul' le_rfl hx.1))
    · have hu : current k x ≤ ENNReal.ofReal (N k ^ (-e + τ)) :=
        hcur.trans ((mul_le_mul' (ENNReal.ofReal_le_ofReal hK₃) hx.2).trans hhigh)
      exact (not_lt_of_ge hu hbad).elim
  calc
    μ k {x | current k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < current k x} ≤
        μ k {x | current k x < ENNReal.ofReal (N k ^ (-(τ / 3))) * old k x} :=
      measure_mono_ae hincl
    _ ≤ ENNReal.ofReal (N k ^ (-(τ / 3)) * K k) := hdropk
    _ ≤ ENNReal.ofReal (N k ^ (-(τ / 6))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        N k ^ (-(τ / 3)) * K k ≤ N k ^ (-(τ / 3)) * N k ^ (τ / 6) :=
          mul_le_mul_of_nonneg_left hK₆ (Real.rpow_nonneg hNk.le _)
        _ = N k ^ (-(τ / 6)) := by
          rw [← Real.rpow_add hNk]
          congr 1
          ring

/-- Nested observations extend typical density exponents from any dense depth grid
to every depth. Continuity of the limiting profile supplies arbitrarily close
bracketing exponents; only two exceptional sets are used for each depth/tolerance. -/
theorem hasTypicalDensity_of_dense_antitone {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (g : ℝ → (k : ℕ) → α k → ℝ≥0∞) (f : ℝ → ℝ) (hf : Continuous f)
    (grid : Set ℝ) (hgrid : Dense grid)
    (htypical : ∀ r ∈ grid, HasTypicalDensity N μ (g r) (f r))
    (hmono : ∀ r s : ℝ, r ≤ s → ∀ k, ∀ᵐ x ∂μ k, g s k x ≤ g r k x) :
    ∀ r : ℝ, HasTypicalDensity N μ (g r) (f r) := by
  intro r τ hτ
  have hτ₂ : 0 < τ / 2 := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := r)) (τ / 2) hτ₂
  obtain ⟨lo, hloGrid, hlo⟩ := hgrid.exists_between (show r - δ < r by linarith)
  obtain ⟨hi, hhiGrid, hhi⟩ := hgrid.exists_between (show r < r + δ by linarith)
  have hfl : |f lo - f r| < τ / 2 := by
    simpa only [Real.dist_eq] using hfδ (show dist lo r < δ by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlo.2)]
      linarith [hlo.1])
  have hfh : |f hi - f r| < τ / 2 := by
    simpa only [Real.dist_eq] using hfδ (show dist hi r < δ by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hhi.1)]
      linarith [hhi.2])
  let bad : ℝ → (k : ℕ) → Set (α k) := fun q k =>
    {x | g q k x < ENNReal.ofReal (N k ^ (-f q - τ / 2)) ∨
      ENNReal.ofReal (N k ^ (-f q + τ / 2)) < g q k x}
  have hsmallLo : IsPowerSmall N (fun k => μ k (bad lo k)) := htypical lo hloGrid (τ / 2) hτ₂
  have hsmallHi : IsPowerSmall N (fun k => μ k (bad hi k)) := htypical hi hhiGrid (τ / 2) hτ₂
  apply (hsmallLo.add hN hsmallHi).mono
  apply Eventually.of_forall
  intro k
  have hset : ∀ᵐ x ∂μ k,
      (g r k x < ENNReal.ofReal (N k ^ (-f r - τ)) ∨
        ENNReal.ofReal (N k ^ (-f r + τ)) < g r k x) →
      x ∈ bad lo k ∪ bad hi k := by
    filter_upwards [hmono lo r hlo.2.le k, hmono r hi hhi.1.le k] with x hxlo hxhi hbad
    by_cases hxl : x ∈ bad lo k
    · exact Or.inl hxl
    by_cases hxh : x ∈ bad hi k
    · exact Or.inr hxh
    simp only [bad, mem_ofPred_eq, not_or, not_lt] at hxl hxh
    have hlow : ENNReal.ofReal (N k ^ (-f r - τ)) ≤
        ENNReal.ofReal (N k ^ (-f hi - τ / 2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le (hN₁ k)
      linarith [(abs_lt.mp hfh).2]
    have hhigh : ENNReal.ofReal (N k ^ (-f lo + τ / 2)) ≤
        ENNReal.ofReal (N k ^ (-f r + τ)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_le (hN₁ k)
      linarith [(abs_lt.mp hfl).1]
    rcases hbad with hbad | hbad
    · exact (not_lt_of_ge (hlow.trans (hxh.1.trans hxhi)) hbad).elim
    · exact (not_lt_of_ge (hxlo.trans (hxl.2.trans hhigh)) hbad).elim
  exact (measure_mono_ae hset).trans (measure_union_le _ _)

end Submission.Obl.k4_native_grid_profile_extension.Profiles
