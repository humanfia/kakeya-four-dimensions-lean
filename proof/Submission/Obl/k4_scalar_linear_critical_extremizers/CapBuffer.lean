/-
Adapted from: here:o093
Own proofs by session x0318, branch ae1ecd4; scalar chart interfaces by
session x0364 in the same LOT tree. The source module is
Submission/Obl/k4_scalar_critical_path_terminal/CapBuffer.lean.
-/

import Submission.Obl.k4_scalar_linear_critical_extremizers.ConcreteProfiles

namespace Submission.Obl.k4_scalar_linear_critical_extremizers.Split

open Set Filter
open scoped Topology

noncomputable section

/-- Enlarge the actual density caps slowly enough to absorb uniform
profile errors, while keeping every buffered cap strictly below one. -/
theorem exists_slow_cap_buffer (dim err : ℕ → ℝ) (dstar : ℝ) (hstar : dstar < 1)
    (hdim : ∀ i, dstar ≤ dim i ∧ dim i < 1)
    (hdimlim : Tendsto dim atTop (𝓝 dstar))
    (herr : ∀ i, 0 ≤ err i) (herrlim : Tendsto err atTop (𝓝 0)) :
    ∃ caps : ℕ → ℝ, (∀ i, dim i ≤ caps i ∧ dstar < caps i ∧ caps i < 1) ∧
      Tendsto caps atTop (𝓝 dstar) ∧
      Tendsto (fun i => err i / (caps i - dstar)) atTop (𝓝 0) := by
  let c := (1 - dstar) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hc₁ : c < 1 - dstar := by dsimp [c]; linarith
  let tol := fun i : ℕ => 1 / ((i : ℝ) + 1)
  have htol (i : ℕ) : 0 < tol i := by dsimp [tol]; positivity
  have htollim : Tendsto tol atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsqrt : Tendsto (fun i => Real.sqrt (err i)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp herrlim
  let τ := fun i => Real.sqrt (err i) + tol i
  have hτ (i : ℕ) : 0 < τ i := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (htol i)
  have hτlim : Tendsto τ atTop (𝓝 0) := by simpa only [add_zero] using hsqrt.add htollim
  let β := fun i => max (dim i - dstar) (min c (τ i))
  have hβ (i : ℕ) : 0 < β i :=
    (lt_min hc (hτ i)).trans_le (le_max_right _ _)
  have hβ₁ (i : ℕ) : β i < 1 - dstar :=
    max_lt (by linarith [(hdim i).2]) ((min_le_left _ _).trans_lt hc₁)
  have hdiff : Tendsto (fun i => dim i - dstar) atTop (𝓝 0) := by
    simpa only [sub_self] using hdimlim.sub (tendsto_const_nhds (x := dstar))
  have hmin : Tendsto (fun i => min c (τ i)) atTop (𝓝 0) := by
    simpa only [min_eq_right hc.le] using (tendsto_const_nhds (x := c)).min hτlim
  have hβlim : Tendsto β atTop (𝓝 0) := by
    simpa only [max_self] using hdiff.max hmin
  let caps := fun i => dstar + β i
  have hcaps (i : ℕ) : dim i ≤ caps i ∧ dstar < caps i ∧ caps i < 1 := by
    have hdimβ := le_max_left (dim i - dstar) (min c (τ i))
    dsimp [caps]
    exact ⟨by linarith, by linarith [hβ i], by linarith [hβ₁ i]⟩
  have hcapslim : Tendsto caps atTop (𝓝 dstar) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := dstar)).add hβlim
  have hratio : Tendsto (fun i => err i / β i) atTop (𝓝 0) := by
    have hupperlim : Tendsto (fun i => err i / c + Real.sqrt (err i)) atTop (𝓝 0) := by
      simpa only [zero_div, zero_add] using (herrlim.div_const c).add hsqrt
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupperlim
      (fun i => div_nonneg (herr i) (hβ i).le)
    intro i
    by_cases hcτ : c ≤ τ i
    · have hcβ : c ≤ β i := by
        simpa only [β, min_eq_left hcτ] using le_max_right (dim i - dstar) (min c (τ i))
      exact (div_le_div_of_nonneg_left (herr i) hc hcβ).trans
        (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    · have hτβ : τ i ≤ β i := by
        simpa only [β, min_eq_right (le_of_not_ge hcτ)] using
          le_max_right (dim i - dstar) (min c (τ i))
      have hsβ : Real.sqrt (err i) ≤ β i :=
        (le_add_of_nonneg_right (htol i).le).trans hτβ
      have hle : err i / β i ≤ Real.sqrt (err i) := by
        apply (div_le_iff₀ (hβ i)).2
        have hmul := mul_le_mul_of_nonneg_left hsβ (Real.sqrt_nonneg (err i))
        nlinarith [Real.sq_sqrt (herr i)]
      exact hle.trans (le_add_of_nonneg_left (div_nonneg (herr i) hc.le))
  refine ⟨caps, hcaps, hcapslim, ?_⟩
  convert hratio using 1
  funext i
  dsimp [caps]
  ring

end

end Submission.Obl.k4_scalar_linear_critical_extremizers.Split
