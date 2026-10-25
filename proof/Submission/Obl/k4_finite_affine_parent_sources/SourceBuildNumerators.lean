-- Adapted from this LOT tree, o232/x0812 f7bed5fb, Submission/Obl/k4_finite_positive_prepared_models/SourceBuildNumerators.lean; namespace renamed.
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildCodes
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionNumerator

/-!
# End-history numerators and the kept states of the window parent

`end_bin_numerator`: the window numerator of the parent (per end history and original planar
velocity code, `window_parent_original`) and a palette `π` dominating every per-code numerator
of the parent's reference law (x0807's palette) give, for every measurable `S2 ⊆ S1`, end
history `h` and native velocity bin of width at least `2 blur`,

  `(ν × dt)(S2 ∩ {end = h} ∩ bin) ≤ 4 C (ν × dt)(S0 ∩ par ∩ {end = h}) π(bin)`.

`kept_deleted_le`: keeping only the states (end history, state code) with the floor
`δ w(h)` deletes at most `81 K δ Σ_h w(h)` when every end history carries at most `81 K` codes.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

local instance optMeasBN (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingBN (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- A set of incidences inside the unit time window has finite product mass. -/
theorem prod_ne_top_of_unit {ν₀ : Measure Trajectory} [IsProbabilityMeasure ν₀]
    {X : Set Incidence} (hX : X ⊆ univ ×ˢ Icc (0 : ℝ) 1) : (ν₀.prod volume) X ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono hX)
  rw [Measure.prod_prod, Real.volume_Icc]
  simp

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **End-history numerators of retained subsets of the window parent.** -/
theorem end_bin_numerator (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hEm : ∀ w, MeasurableSet (E w))
    (w₀ : Fin W) (i e : ℕ) (b₀ : Fin p.C) (δv : ℝ)
    (S0w : Set Incidence) (hS0m : MeasurableSet S0w) (hS0E : S0w ⊆ E w₀)
    (S1 : Set Incidence) (hS1 : S1 ⊆ S0w ∩ {x | p.history m i (w₀, x) = some b₀})
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hwin : ∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
      ((ν w₀).prod volume).real (S1 ∩
        {x | p.history m e (w₀, x) = h ∧ worldBin δv (w₀, x) = z}) ≤
      Cw * ((ν w₀).prod volume).real (S0w ∩ {x | p.history m i (w₀, x) = some b₀} ∩
          {x | p.history m e (w₀, x) = h}) *
        (((ν w₀).prod volume).real (S0w ∩ {x | p.history m i (w₀, x) = some b₀} ∩
            {x | worldBin δv (w₀, x) = z}) /
          ((ν w₀).prod volume).real (S0w ∩ {x | p.history m i (w₀, x) = some b₀})))
    (hR0 : ((ν w₀).prod volume) (S0w ∩ {x | p.history m i (w₀, x) = some b₀}) ≠ 0)
    (π : Measure ℝ) (V : Incidence → ℝ) {blur : ℝ}
    (hdom : ∀ (ρ : Measure Incidence), ρ ≤ nuE (((ν w₀).prod volume).restrict (E w₀))
        (S0w ∩ {x | p.history m i (w₀, x) = some b₀}) →
      ∀ (P : Set Incidence) (C : ENNReal) (width : ℝ), 2 * blur ≤ width →
      (∀ z : Fin 2 → ℤ, ρ (P ∩ {x | worldBin δv (w₀, x) = z}) ≤
        C * nuE (((ν w₀).prod volume).restrict (E w₀))
          (S0w ∩ {x | p.history m i (w₀, x) = some b₀}) {x | worldBin δv (w₀, x) = z}) →
      ∀ e' : ℤ, ρ (P ∩ {x | ⌊V x / width⌋ = e'}) ≤ 4 * C * π {w | ⌊w / width⌋ = e'})
    (S2 : Set Incidence) (hS2m : MeasurableSet S2) (hS21 : S2 ⊆ S1)
    {width : ℝ} (hwidth : 2 * blur ≤ width) (h : Option (Fin p.C)) (e' : ℤ) :
    ((ν w₀).prod volume) (S2 ∩ ({x | p.history m e (w₀, x) = h} ∩
        {x | ⌊V x / width⌋ = e'})) ≤
      4 * ENNReal.ofReal Cw * ((ν w₀).prod volume) (S0w ∩
        {x | p.history m i (w₀, x) = some b₀} ∩ {x | p.history m e (w₀, x) = h}) *
        π {w | ⌊w / width⌋ = e'} := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  set μ := ((ν w₀).prod volume).restrict (E w₀) with hμ
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact lt_top_iff_ne_top.mpr (prod_ne_top_of_unit (hE w₀))
  have hpar : MeasurableSet {x : Incidence | p.history m i (w₀, x) = some b₀} :=
    (hp.measurable_history _).comp measurable_prodMk_left (measurableSet_singleton _)
  have hend : MeasurableSet {x : Incidence | p.history m e (w₀, x) = h} :=
    (hp.measurable_history _).comp measurable_prodMk_left (measurableSet_singleton _)
  set R := S0w ∩ {x | p.history m i (w₀, x) = some b₀} with hRdef
  have hRm : MeasurableSet R := hS0m.inter hpar
  have hRE : R ⊆ E w₀ := fun x hx => hS0E hx.1
  have hRt : ((ν w₀).prod volume) R ≠ ⊤ := prod_ne_top_of_unit ((hRE).trans (hE w₀))
  have hμR : μ R = ((ν w₀).prod volume) R := by
    rw [hμ, Measure.restrict_apply hRm, inter_eq_left.mpr hRE]
  have hU : Measurable (fun x : Incidence => worldBin δv (w₀, x)) :=
    (measurable_worldBin δv).comp measurable_prodMk_left
  set T := S2 ∩ {x | p.history m e (w₀, x) = h} with hTdef
  have hTm : MeasurableSet T := hS2m.inter hend
  have hTR : T ⊆ R := fun x hx => hS1 (hS21 hx.1)
  have hTE : T ⊆ E w₀ := hTR.trans hRE
  -- the per-code numerator
  set c := ENNReal.ofReal Cw * ((ν w₀).prod volume) (R ∩ {x | p.history m e (w₀, x) = h})
    with hc
  have hcode : ∀ z : Fin 2 → ℤ, μ (T ∩ (fun x => worldBin δv (w₀, x)) ⁻¹' {z}) ≤
      c * nuE μ R ((fun x => worldBin δv (w₀, x)) ⁻¹' {z}) := by
    intro z
    have hZm : MeasurableSet ((fun x : Incidence => worldBin δv (w₀, x)) ⁻¹' {z}) :=
      hU (measurableSet_singleton z)
    have hX : T ∩ (fun x => worldBin δv (w₀, x)) ⁻¹' {z} ⊆
        S1 ∩ {x | p.history m e (w₀, x) = h ∧ worldBin δv (w₀, x) = z} := by
      intro x hx
      exact ⟨hS21 hx.1.1, hx.1.2, hx.2⟩
    have hS1t : S1 ∩ {x | p.history m e (w₀, x) = h ∧ worldBin δv (w₀, x) = z} ⊆
        univ ×ˢ Icc (0 : ℝ) 1 := fun x hx => hE w₀ (hS0E (hS1 hx.1).1)
    have hRht : ((ν w₀).prod volume) (R ∩ {x | p.history m e (w₀, x) = h}) ≠ ⊤ :=
      prod_ne_top_of_unit (fun x hx => hE w₀ (hRE hx.1))
    have hRzt : ((ν w₀).prod volume) (R ∩ {x | worldBin δv (w₀, x) = z}) ≠ ⊤ :=
      prod_ne_top_of_unit (fun x hx => hE w₀ (hRE hx.1))
    have hRpos : 0 < ((ν w₀).prod volume).real R := by
      rw [measureReal_def]; exact ENNReal.toReal_pos hR0 hRt
    have hw := hwin h z
    -- the left side
    have hL : μ (T ∩ (fun x => worldBin δv (w₀, x)) ⁻¹' {z}) ≤
        ENNReal.ofReal (((ν w₀).prod volume).real
          (S1 ∩ {x | p.history m e (w₀, x) = h ∧ worldBin δv (w₀, x) = z})) := by
      rw [ofReal_measureReal (prod_ne_top_of_unit hS1t)]
      calc μ (T ∩ (fun x => worldBin δv (w₀, x)) ⁻¹' {z})
          ≤ ((ν w₀).prod volume) (T ∩ (fun x => worldBin δv (w₀, x)) ⁻¹' {z}) := by
            rw [hμ]; exact Measure.restrict_le_self _
        _ ≤ _ := measure_mono hX
    refine hL.trans ((ENNReal.ofReal_le_ofReal hw).trans ?_)
    -- the right side
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCw,
      ofReal_measureReal hRht, ENNReal.ofReal_div_of_pos hRpos, ofReal_measureReal hRzt,
      ofReal_measureReal hRt]
    rw [nuE, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hZm, hμR, hμ,
      Measure.restrict_apply (hZm.inter hRm)]
    have hset : (fun x : Incidence => worldBin δv (w₀, x)) ⁻¹' {z} ∩ R ∩ E w₀ =
        R ∩ {x | worldBin δv (w₀, x) = z} := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, hRE h1⟩
    rw [hset, hc, ENNReal.div_eq_inv_mul]
  -- the native bins
  have hbin := bin_numerator μ R T hRm hTm hTR (by rw [hμR]; exact hR0)
    (fun x => worldBin δv (w₀, x)) hU V π hdom c hcode hwidth e'
  have hTbin : μ (T ∩ {z | ⌊V z / width⌋ = e'}) =
      ((ν w₀).prod volume) (S2 ∩ ({x | p.history m e (w₀, x) = h} ∩
        {x | ⌊V x / width⌋ = e'})) := by
    rw [hμ, Measure.restrict_apply' (hEm w₀)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, hTdef]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, -⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, hTE ⟨h1, h2⟩⟩
  rw [← hTbin]
  calc μ (T ∩ {z | ⌊V z / width⌋ = e'}) ≤ 4 * c * π {w | ⌊w / width⌋ = e'} := hbin
    _ = _ := by rw [hc]; ring

/-- **The kept states delete little.** -/
theorem kept_deleted_le (w₀ : Fin W) (e : ℕ) (S2 : Set Incidence) (hS2m : MeasurableSet S2)
    (code : Incidence → (Fin 4 → ℤ)) (hcode : Measurable code)
    (wt : Option (Fin p.C) → ENNReal) (δs : ENNReal) {Kc : ℝ}
    (hV : ∀ h : Option (Fin p.C), ∃ V : Finset (Fin 4 → ℤ), (V.card : ℝ) ≤ 81 * Kc ∧
      ∀ x ∈ S2, p.history m e (w₀, x) = h → code x ∈ V) :
    ((ν w₀).prod volume) (S2 \ keptSet (((ν w₀).prod volume).restrict S2)
        (fun x => p.history m e (w₀, x)) code wt δs) ≤
      ENNReal.ofReal (81 * Kc) * δs * ∑ h, wt h := by
  choose V hVc hVm using hV
  have hend : Measurable (fun x : Incidence => p.history m e (w₀, x)) :=
    (hp.measurable_history _).comp measurable_prodMk_left
  have hkm := measurableSet_keptSet (lam := ((ν w₀).prod volume).restrict S2) hend hcode wt δs
  have hzero : ∀ h, (((ν w₀).prod volume).restrict S2)
      ({x | p.history m e (w₀, x) = h} ∩ {x | code x ∉ V h}) = 0 := by
    intro h
    rw [Measure.restrict_apply' hS2m]
    convert measure_empty (μ := (ν w₀).prod volume)
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hh hc
    exact hh.2 (hVm h x hc hh.1)
  have hdel := deleted_le (lam := ((ν w₀).prod volume).restrict S2)
    (endL := fun x => p.history m e (w₀, x)) (code := code) wt δs V hzero
  rw [Measure.restrict_apply hkm.compl] at hdel
  calc ((ν w₀).prod volume) (S2 \ keptSet (((ν w₀).prod volume).restrict S2)
        (fun x => p.history m e (w₀, x)) code wt δs)
      = ((ν w₀).prod volume) ((keptSet (((ν w₀).prod volume).restrict S2)
        (fun x => p.history m e (w₀, x)) code wt δs)ᶜ ∩ S2) := by
        rw [diff_eq, inter_comm]
    _ ≤ ∑ h, ((V h).card : ENNReal) * (δs * wt h) := hdel
    _ ≤ ∑ h, ENNReal.ofReal (81 * Kc) * (δs * wt h) := by
        refine Finset.sum_le_sum fun h _ => ?_
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (hVc h)
    _ = ENNReal.ofReal (81 * Kc) * δs * ∑ h, wt h := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        ring

end

end

end Submission.Obl.k4_finite_affine_parent_sources
