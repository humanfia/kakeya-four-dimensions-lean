-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceWindow

/-!
# The parent numerator in original units

The fixed prepared law `μ₀ = WorldPath.probability ν ω S0` charges a world slice exactly as
`Z⁻¹ ω (ν × dt)` on `S0`. The window numerator of `exists_window_parent` therefore becomes, in
the original law of the parent's world `w₀` and for the retained parent incidences
`S1 = D_{w₀} ∩ S0_{w₀} ∩ par`,

  `(ν × dt) (S1 ∩ {end = h, vbin = z}) ≤ C (ν × dt) (S0 ∩ par ∩ {end = h}) · π_A {z}`,

where `π_A` is the original conditional law of the planar velocity bin given the parent, under
the fixed law. The normalising constants cancel exactly.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

local instance optMeasSN (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingSN (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- An incidence whose history at some level is a label lies in that label's world and is
counted by it. -/
theorem history_some {i : ℕ} {b₀ : Fin p.C} {y : Fin W × Incidence}
    (hy : p.history m i y = some b₀) : y.1 = p.world b₀ ∧ y.2 ∈ p.counted b₀ := by
  cases hcode : p.terminalCode m y with
  | none =>
    simp [PathData.history, hcode, PathData.ancestorCode] at hy
  | some bt =>
    have hspec := p.terminalCode_spec m hcode
    simp only [PathData.history, Function.comp_apply, hcode, PathData.ancestorCode,
      Option.map_some, Option.some.injEq] at hy
    by_cases hi : i ≤ p.lev bt
    · obtain ⟨-, hw, hsub⟩ := hp.ancestor bt i hi
      rw [hy] at hw hsub
      exact ⟨hspec.2.1.symm.trans hw.symm, hsub hspec.2.2⟩
    · have h0 : p.lev bt - i = 0 := by omega
      have hbt : forestAncestor p.lev p.par bt i = bt := by
        simp only [forestAncestor, h0, Function.iterate_zero, id_eq]
      rw [hbt] at hy
      rw [← hy]
      exact ⟨hspec.2.1.symm, hspec.2.2⟩

/-- The parent event of the fixed law is a single world slice. -/
theorem parent_slice {i : ℕ} (b₀ : Fin p.C) (X : Set (Fin W × Incidence)) :
    X ∩ {y | p.history m i y = some b₀} =
      {p.world b₀} ×ˢ {z | (p.world b₀, z) ∈ X ∩ {y | p.history m i y = some b₀}} := by
  ext ⟨w, z⟩
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_singleton_iff]
  constructor
  · rintro ⟨hX, hh⟩
    have hw := (history_some hp hh).1
    simp only at hw
    subst hw
    exact ⟨rfl, hX, hh⟩
  · rintro ⟨rfl, hX, hh⟩
    exact ⟨hX, hh⟩

/-- The real slice formula of the fixed law. -/
theorem probability_slice_real (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (S0 : Fin W → Set Incidence) (hS0t : ∀ w, S0 w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hpos : WorldPath.original ν ω S0 univ ≠ 0) (w : Fin W) {A : Set Incidence}
    (hA : MeasurableSet A) :
    (WorldPath.probability ν ω S0).real ({w} ×ˢ A) =
      ((WorldPath.original ν ω S0 univ).toReal)⁻¹ * ω w *
        ((ν w).prod volume).real (A ∩ S0 w) := by
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  obtain ⟨-, hslices⟩ := WorldPath.probability_spec ν ω hω0 hω1 S0 hS0t hpos
  rw [measureReal_def, hslices w A hA, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (hω0 w), measureReal_def]

/-- **The window numerator in original units.** -/
theorem numerator_original (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (S0 : Fin W → Set Incidence) (hS0m : ∀ w, MeasurableSet (S0 w))
    (hS0t : ∀ w, S0 w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hpos : WorldPath.original ν ω S0 univ ≠ 0)
    {i i' : ℕ} {b₀ : Fin p.C} (hω₀ : 0 < ω (p.world b₀))
    {D : Set (Fin W × Incidence)} (hD : MeasurableSet D) (δv C : ℝ)
    (hnum : ∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
      (WorldPath.probability ν ω S0).real
          ({y | (p.history m i' y, worldBin δv y) = (h, z)} ∩
            {y | p.history m i y = some b₀} ∩ D) ≤
        C * (WorldPath.probability ν ω S0).real
            ({y | p.history m i' y = h} ∩ {y | p.history m i y = some b₀}) *
          (WorldPath.probability ν ω S0).real
            ({y | worldBin δv y = z} ∩ {y | p.history m i y = some b₀}) /
          (WorldPath.probability ν ω S0).real {y | p.history m i y = some b₀})
    (h : Option (Fin p.C)) (z : Fin 2 → ℤ) :
    ((ν (p.world b₀)).prod volume).real
        ({x | (p.world b₀, x) ∈ D} ∩ S0 (p.world b₀) ∩
          {x | p.history m i (p.world b₀, x) = some b₀} ∩
          {x | p.history m i' (p.world b₀, x) = h ∧ worldBin δv (p.world b₀, x) = z}) ≤
      C * ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
          {x | p.history m i (p.world b₀, x) = some b₀} ∩
          {x | p.history m i' (p.world b₀, x) = h}) *
        (((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
            {x | p.history m i (p.world b₀, x) = some b₀} ∩
            {x | worldBin δv (p.world b₀, x) = z}) /
          ((ν (p.world b₀)).prod volume).real (S0 (p.world b₀) ∩
            {x | p.history m i (p.world b₀, x) = some b₀})) := by
  set w₀ := p.world b₀ with hw₀
  set μ₀ := WorldPath.probability ν ω S0
  set c := ((WorldPath.original ν ω S0 univ).toReal)⁻¹ * ω w₀ with hc
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hZt : WorldPath.original ν ω S0 univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (WorldPath.original_mass_le_one ν ω hω0 hω1 S0 hS0t)
  have hc0 : 0 < c := mul_pos (inv_pos.mpr (ENNReal.toReal_pos hpos hZt)) hω₀
  have hsec : Measurable (fun x : Incidence => ((w₀, x) : Fin W × Incidence)) :=
    measurable_const.prodMk measurable_id
  have hhist (j : ℕ) (a : Option (Fin p.C)) :
      MeasurableSet {x : Incidence | p.history m j (w₀, x) = a} :=
    ((hp.measurable_history j).comp hsec) (measurableSet_singleton a)
  have hbin (zz : Fin 2 → ℤ) : MeasurableSet {x : Incidence | worldBin δv (w₀, x) = zz} :=
    ((measurable_worldBin δv).comp hsec) (measurableSet_singleton zz)
  have hDs : MeasurableSet {x : Incidence | (w₀, x) ∈ D} := hsec hD
  have hslice : ∀ {A : Set Incidence}, MeasurableSet A →
      μ₀.real ({w₀} ×ˢ A) = c * ((ν w₀).prod volume).real (A ∩ S0 w₀) :=
    fun hA => probability_slice_real hp hν hω0 hω1 S0 hS0t hpos w₀ hA
  -- the four world slices
  have e1 : μ₀.real ({y | (p.history m i' y, worldBin δv y) = (h, z)} ∩
      {y | p.history m i y = some b₀} ∩ D) =
      c * ((ν w₀).prod volume).real ({x | (w₀, x) ∈ D} ∩ S0 w₀ ∩
          {x | p.history m i (w₀, x) = some b₀} ∩
          {x | p.history m i' (w₀, x) = h ∧ worldBin δv (w₀, x) = z}) := by
    have hset : {y | (p.history m i' y, worldBin δv y) = (h, z)} ∩
        {y | p.history m i y = some b₀} ∩ D =
        {w₀} ×ˢ ({x | (w₀, x) ∈ D} ∩ {x | p.history m i (w₀, x) = some b₀} ∩
          {x | p.history m i' (w₀, x) = h ∧ worldBin δv (w₀, x) = z}) := by
      rw [show {y | (p.history m i' y, worldBin δv y) = (h, z)} ∩
          {y | p.history m i y = some b₀} ∩ D =
          ({y | (p.history m i' y, worldBin δv y) = (h, z)} ∩ D) ∩
          {y | p.history m i y = some b₀} by
        ext y; simp only [mem_inter_iff]; tauto, parent_slice hp b₀]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, Prod.mk.injEq]
      tauto
    have hm1 : MeasurableSet ({x | (w₀, x) ∈ D} ∩ {x | p.history m i (w₀, x) = some b₀} ∩
        {x | p.history m i' (w₀, x) = h ∧ worldBin δv (w₀, x) = z}) :=
      (hDs.inter (hhist i _)).inter ((hhist i' h).inter (hbin z))
    rw [hset, hslice hm1]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have e2 : μ₀.real ({y | p.history m i' y = h} ∩ {y | p.history m i y = some b₀}) =
      c * ((ν w₀).prod volume).real (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀} ∩
        {x | p.history m i' (w₀, x) = h}) := by
    rw [parent_slice hp b₀]
    have hm : MeasurableSet {x | (w₀, x) ∈ {y | p.history m i' y = h} ∩
        {y | p.history m i y = some b₀}} := (hhist i' h).inter (hhist i _)
    rw [hslice hm]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have e3 : μ₀.real ({y | worldBin δv y = z} ∩ {y | p.history m i y = some b₀}) =
      c * ((ν w₀).prod volume).real (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀} ∩
        {x | worldBin δv (w₀, x) = z}) := by
    rw [parent_slice hp b₀]
    have hm : MeasurableSet {x | (w₀, x) ∈ {y | worldBin δv y = z} ∩
        {y | p.history m i y = some b₀}} := (hbin z).inter (hhist i _)
    rw [hslice hm]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  have e4 : μ₀.real {y | p.history m i y = some b₀} =
      c * ((ν w₀).prod volume).real (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀}) := by
    rw [← univ_inter {y | p.history m i y = some b₀}, parent_slice hp b₀]
    have hm : MeasurableSet {x | (w₀, x) ∈ univ ∩ {y | p.history m i y = some b₀}} := by
      convert hhist i (some b₀) using 1
      ext x
      simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq]
    rw [hslice hm]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_univ, true_and]
    tauto
  have hn := hnum h z
  rw [e1, e2, e3, e4] at hn
  set a := ((ν w₀).prod volume).real ({x | (w₀, x) ∈ D} ∩ S0 w₀ ∩
          {x | p.history m i (w₀, x) = some b₀} ∩
          {x | p.history m i' (w₀, x) = h ∧ worldBin δv (w₀, x) = z})
  set bb := ((ν w₀).prod volume).real (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀} ∩
        {x | p.history m i' (w₀, x) = h})
  set dd := ((ν w₀).prod volume).real (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀} ∩
        {x | worldBin δv (w₀, x) = z})
  set ee := ((ν w₀).prod volume).real (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀})
  have hfin : ((ν w₀).prod volume) (S0 w₀ ∩ {x | p.history m i (w₀, x) = some b₀}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (inter_subset_left.trans (hS0t w₀)))
    rw [Measure.prod_prod]
    simp
  rcases eq_or_lt_of_le (measureReal_nonneg : (0 : ℝ) ≤ ee) with he | he
  · -- an empty parent: the left side vanishes
    have hee : ee = 0 := he.symm
    have ha0 : a ≤ ee := measureReal_mono (fun x hx => ⟨hx.1.1.2, hx.1.2⟩) hfin
    rw [hee] at ha0
    have ha : a = 0 := le_antisymm ha0 measureReal_nonneg
    rw [ha, hee, div_zero, mul_zero]
  · have hce : 0 < c * ee := mul_pos hc0 he
    have key : c * a ≤ c * (C * bb * (dd / ee)) := by
      calc c * a ≤ C * (c * bb) * (c * dd) / (c * ee) := hn
        _ = c * (C * bb * (dd / ee)) := by field_simp
    exact le_of_mul_le_mul_left key hc0

end

end

end Submission.Obl.k4_finite_affine_parent_sources
