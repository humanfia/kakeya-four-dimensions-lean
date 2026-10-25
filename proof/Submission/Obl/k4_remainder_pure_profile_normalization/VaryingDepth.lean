/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/VaryingDepth.lean.
-/
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileGrid

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Set Filter MeasureTheory
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped Topology ENNReal

/-- Density typicality ignores changes on an eventual family of null sets. -/
theorem typicalDensity_congr_eventually_ae {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    {N : ℕ → ℝ} {μ : (k : ℕ) → Measure (α k)}
    {g d : (k : ℕ) → α k → ENNReal} {e : ℝ}
    (hg : HasTypicalDensity N μ g e) (heq : ∀ᶠ k in atTop, d k =ᵐ[μ k] g k) :
    HasTypicalDensity N μ d e := by
  intro τ hτ
  obtain ⟨c, hc, hb⟩ := hg τ hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [heq, hb] with k hk hbk
  have hsets : {x | d k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < d k x} =ᵐ[μ k]
      {x | g k x < ENNReal.ofReal (N k ^ (-e - τ)) ∨
        ENNReal.ofReal (N k ^ (-e + τ)) < g k x} := by
    filter_upwards [hk] with x hx
    simp only [hx]
  exact (measure_congr hsets).trans_le hbk

/-- A converging resolution-dependent depth has the expected fixed exponent.
The comparison uses two fixed depths for each tolerance, so it needs no uniform
typicality assumption over the depth parameter. -/
theorem typicalDensity_at_tendsto_depth {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k)) (g : ℝ → (k : ℕ) → α k → ENNReal)
    (f : ℝ → ℝ) (hf : Continuous f)
    (htyp : ∀ r, HasTypicalDensity N μ (g r) (f r))
    (hmono : ∀ r s, r ≤ s → ∀ k, ∀ᵐ x ∂μ k, g s k x ≤ g r k x)
    {a : ℕ → ℝ} {r : ℝ} (ha : Tendsto a atTop (𝓝 r)) :
    HasTypicalDensity N μ (fun k => g (a k) k) (f r) := by
  intro τ hτ
  have hτ₂ : 0 < τ / 2 := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := r)) (τ / 2) hτ₂
  let lo := r - δ / 2
  let hi := r + δ / 2
  have hlo : lo < r := by dsimp [lo]; linarith
  have hhi : r < hi := by dsimp [hi]; linarith
  have hfl : |f lo - f r| < τ / 2 := by
    apply hfδ
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hlo)]
    dsimp [lo]
    linarith
  have hfh : |f hi - f r| < τ / 2 := by
    apply hfδ
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hhi)]
    dsimp [hi]
    linarith
  let bad (q : ℝ) (k : ℕ) := {x | g q k x < ENNReal.ofReal (N k ^ (-f q - τ / 2)) ∨
    ENNReal.ofReal (N k ^ (-f q + τ / 2)) < g q k x}
  have hsmallLo : IsPowerSmall N (fun k => μ k (bad lo k)) := htyp lo (τ / 2) hτ₂
  have hsmallHi : IsPowerSmall N (fun k => μ k (bad hi k)) := htyp hi (τ / 2) hτ₂
  apply (hsmallLo.add hN hsmallHi).mono
  filter_upwards [ha.eventually (Ioo_mem_nhds hlo hhi)] with k hk
  have hevent : ∀ᵐ x ∂μ k,
      (g (a k) k x < ENNReal.ofReal (N k ^ (-f r - τ)) ∨
        ENNReal.ofReal (N k ^ (-f r + τ)) < g (a k) k x) → x ∈ bad lo k ∪ bad hi k := by
    filter_upwards [hmono lo (a k) hk.1.le k, hmono (a k) hi hk.2.le k]
      with x hupper hlower hbad
    by_contra hx
    have hgoodLo : ENNReal.ofReal (N k ^ (-f lo - τ / 2)) ≤ g lo k x ∧
        g lo k x ≤ ENNReal.ofReal (N k ^ (-f lo + τ / 2)) := by
      simpa only [bad, mem_union, mem_ofPred_eq, not_or, not_lt] using (not_or.mp hx).1
    have hgoodHi : ENNReal.ofReal (N k ^ (-f hi - τ / 2)) ≤ g hi k x ∧
        g hi k x ≤ ENNReal.ofReal (N k ^ (-f hi + τ / 2)) := by
      simpa only [bad, mem_union, mem_ofPred_eq, not_or, not_lt] using (not_or.mp hx).2
    have hboundLo : ENNReal.ofReal (N k ^ (-f r - τ)) ≤ g (a k) k x := by
      apply le_trans _ (hgoodHi.1.trans hlower)
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le (hN₁ k) (by linarith [(abs_lt.mp hfh).2])
    have hboundHi : g (a k) k x ≤ ENNReal.ofReal (N k ^ (-f r + τ)) := by
      apply (hupper.trans hgoodLo.2).trans
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_le (hN₁ k) (by linarith [(abs_lt.mp hfl).1])
    exact hbad.elim (not_lt_of_ge hboundLo) (not_lt_of_ge hboundHi)
  exact (measure_mono_ae hevent).trans (measure_union_le _ _)

/-- Clipping supplies the same conclusion at both endpoints of the allowed
interval.  Resolution-dependent depths only need to lie in it eventually. -/
theorem typicalDensity_on_Icc_at_tendsto_depth {α : ℕ → Type*}
    [∀ k, MeasurableSpace (α k)] (N : ℕ → ℝ) (hN₁ : ∀ k, 1 ≤ N k)
    (hN : Tendsto N atTop atTop) (μ : (k : ℕ) → Measure (α k))
    (g : ℝ → (k : ℕ) → α k → ENNReal) (f : ℝ → ℝ)
    {l u : ℝ} (hlu : l ≤ u) (hf : ContinuousOn f (Icc l u))
    (htyp : ∀ r ∈ Icc l u, HasTypicalDensity N μ (g r) (f r))
    (hmono : ∀ r ∈ Icc l u, ∀ s ∈ Icc l u, r ≤ s →
      ∀ k, ∀ᵐ x ∂μ k, g s k x ≤ g r k x)
    {a : ℕ → ℝ} {r : ℝ} (hr : r ∈ Icc l u)
    (ha : Tendsto a atTop (𝓝 r)) (hamem : ∀ᶠ k in atTop, a k ∈ Icc l u) :
    HasTypicalDensity N μ (fun k => g (a k) k) (f r) := by
  let clip (t : ℝ) : ℝ := projIcc l u hlu t
  have hclip : Continuous clip := continuous_subtype_val.comp continuous_projIcc
  have hmem (t : ℝ) : clip t ∈ Icc l u := (projIcc l u hlu t).property
  have hself (t : ℝ) (ht : t ∈ Icc l u) : clip t = t :=
    congrArg Subtype.val (projIcc_of_mem hlu ht)
  have hfc : Continuous (fun t => f (clip t)) := hf.comp_continuous hclip hmem
  have hresult := typicalDensity_at_tendsto_depth N hN₁ hN μ
    (fun t => g (clip t)) (fun t => f (clip t)) hfc
    (fun t => htyp (clip t) (hmem t))
    (fun t s hts => hmono _ (hmem t) _ (hmem s) (monotone_projIcc hlu hts)) ha
  rw [hself r hr] at hresult
  apply typicalDensity_congr_eventually_ae hresult
  filter_upwards [hamem] with k hk
  rw [hself (a k) hk]

end Submission.Obl.k4_remainder_pure_profile_normalization
