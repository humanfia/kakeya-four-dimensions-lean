-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Hierarchy, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Hierarchy.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Hierarchy.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Hierarchy.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Grid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridHierarchy

set_option autoImplicit false

/-!
# The affine hierarchy in version 2 (paper `tex-05`, proof of Prop. `prop:scalar-normal`)

"For `j = 2`, repeat with the second component on these new labels, recomputing `m, δ, τ`
first.  Do the same at every length in the fixed finite hierarchy."

A version-2 hierarchy is one scalar hierarchy (x0662's `ScalarGridHierarchy`, o078 branch `x0662`
at `f2bac599`) per row component, on COMMON retained times.  The extension by one length fits
component `0` (`v2_grid_affine_fit`) and then component `1` on the retained times; the uniform
construction (the `j = 2` counterpart of x0662's `uniform_original_scalar_grid_hierarchy`) pays two
uniform subpower duration losses per length.  The common times let x0662's Taylor/comparison
lemmas (`ScalarHierarchyCurrentTaylor`, `ScalarPrunedHierarchy`) act on both components with one
common retained set.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set Filter
open Submission.Obl.k4_discrete_of_terminal_charts
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- **A version-2 hierarchy**: one scalar hierarchy per component, on common times. -/
structure V2Hierarchy {Λ : Type*} [MeasurableSpace Λ] {n : ℕ} (ν : Measure Λ)
    (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i)
    (p : Fin n → ℝ) (B : ℝ) where
  comp : (k : Fin 2) → ScalarGridHierarchy ν E (fun t => F t k) J hJ p B
  times_eq : (comp 1).times = (comp 0).times

theorem activeTimes_eq_scalarNormalTimes {Λ : Type*} (E : Set (Λ × ℝ)) :
    activeTimes E = scalarNormalTimes E := rfl

theorem exists_initial_v2_hierarchy {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {K : ℝ} (hK : 1 ≤ K)
    (hmass : K⁻¹ ≤ (ν.prod volume).real E) (F : ℝ → Fin 2 → ℝ)
    (J : Fin 0 → ℕ) (hJ : ∀ i, 0 < J i) (p : Fin 0 → ℝ) :
    Nonempty (V2Hierarchy ν E F J hJ p (8 * K)) := by
  obtain ⟨G⟩ := exists_initial_scalar_grid_hierarchy ν hE hunit hK hmass (fun t => F t 0) J hJ p
  let G1 : ScalarGridHierarchy ν E (fun t => F t 1) J hJ p (8 * K) :=
    { times := G.times, slope := G.slope, intercept := G.intercept,
      measurable_times := G.measurable_times, unit_time := G.unit_time,
      active_time := G.active_time, measurable_slope := G.measurable_slope,
      measurable_intercept := G.measurable_intercept, bounded := G.bounded, mass := G.mass,
      time_floor := G.time_floor, constant_on_grid := G.constant_on_grid,
      fit := fun i => Fin.elim0 i }
  let comp : (k : Fin 2) → ScalarGridHierarchy ν E (fun t => F t k) J hJ p (8 * K) :=
    fun k => match k with
      | ⟨0, _⟩ => G
      | ⟨1, _⟩ => G1
  exact ⟨{ comp := comp, times_eq := rfl }⟩

namespace V2Hierarchy

/-- **Extension by one length**: component `0`, then component `1`. -/
theorem extend {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {K B Q₀ Q₁ ζ d : ℝ}
    (J : Fin (n + 1) → ℕ) (hJ : ∀ i, 0 < J i) (p : Fin (n + 1) → ℝ)
    (G : V2Hierarchy ν E F (fun i => J i.succ) (fun i => hJ i.succ) (fun i => p i.succ) B)
    (h : UpperHyp ν c E F K ζ d) (hζ : 0 < ζ) (hKB : K ≤ B)
    (hB : 1 ≤ B) (hQ₀ : 1 ≤ Q₀) (hQ₁ : 1 ≤ Q₁) (hp : ∀ i, 0 ≤ p i)
    (hHp : 1 / (J 0 : ℝ) ≤ p 0) (hζH : ζ ≤ (1 / (J 0 : ℝ)) ^ 2)
    (hfit₀ : V2BlockFitAt (d := d) Λ (8 * B) (p 0) Q₀⁻¹ 0)
    (hfit₁ : V2BlockFitAt (d := d) Λ (8 * scalarGridStageBound B Q₀) (p 0) Q₁⁻¹ 1) :
    Nonempty (V2Hierarchy ν E F J hJ p
      (scalarGridStageBound (scalarGridStageBound B Q₀) Q₁)) := by
  set B₁ := scalarGridStageBound B Q₀ with hB₁def
  set B₂ := scalarGridStageBound B₁ Q₁ with hB₂def
  obtain ⟨h1B₁, hBB₁, h5120B, -⟩ := scalarGridStageBound_bounds hB hQ₀
  obtain ⟨h1B₂, hB₁B₂, h5120B₁, -⟩ := scalarGridStageBound_bounds h1B₁ hQ₁
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hB₁pos : 0 < B₁ := zero_lt_one.trans_le h1B₁
  have hQ₀pos : 0 < Q₀ := zero_lt_one.trans_le hQ₀
  have hQ₁pos : 0 < Q₁ := zero_lt_one.trans_le hQ₁
  set T := (G.comp 0).times with hTdef
  -- component `0` on the old retained times
  let R := E ∩ (univ ×ˢ T)
  have hR : MeasurableSet R :=
    h.event_measurable.inter (MeasurableSet.univ.prod (G.comp 0).measurable_times)
  have hRunit : R ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => h.unit_time hq.1
  have hRnormal : UpperHyp ν c R F B ζ d :=
    (h.restrict_event hR inter_subset_left).increase_constant hζ hKB
  have hRmass : B⁻¹ ≤ (ν.prod volume).real R := by
    have hh := ENNReal.toReal_mono (original_unit_incidence_ne_top ν hR hRunit) (G.comp 0).mass
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hBpos.le)] at hh
    exact hh
  obtain ⟨U₀, A₀, C₀, hU₀m, hU₀unit, hU₀active, hA₀m, hC₀m, hb₀, -, hmass₀,
      hfloor₀, hconst₀, hfit₀'⟩ :=
    v2_grid_affine_fit 0 hRnormal hB hζ (inv_nonneg.mpr hQ₀pos.le) hRmass (hJ 0) hHp hζH hfit₀
  have hU₀T : U₀ ⊆ T := by
    intro t ht
    obtain ⟨l, hl⟩ := hU₀active ht
    exact hl.2.2
  have hRU₀ : R ∩ (univ ×ˢ U₀) = E ∩ (univ ×ˢ U₀) := by
    ext q
    exact ⟨fun hq => ⟨hq.1.1, hq.2⟩, fun hq => ⟨⟨hq.1, mem_univ _, hU₀T hq.2.2⟩, hq.2⟩⟩
  rw [hRU₀] at hmass₀ hfloor₀ hfit₀'
  -- component `1` on the new retained times
  let R₀ := E ∩ (univ ×ˢ U₀)
  have hR₀ : MeasurableSet R₀ := h.event_measurable.inter (MeasurableSet.univ.prod hU₀m)
  have hR₀unit : R₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun q hq => h.unit_time hq.1
  have hR₀normal : UpperHyp ν c R₀ F B₁ ζ d :=
    (h.restrict_event hR₀ inter_subset_left).increase_constant hζ (hKB.trans hBB₁)
  have hR₀mass : B₁⁻¹ ≤ (ν.prod volume).real R₀ := by
    have hh := ENNReal.toReal_mono (original_unit_incidence_ne_top ν hR₀ hR₀unit) hmass₀
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact (scalarGridStageBound_mass hB hQ₀).trans hh
  obtain ⟨U₁, A₁, C₁, hU₁m, hU₁unit, hU₁active, hA₁m, hC₁m, hb₁, -, hmass₁,
      hfloor₁, hconst₁, hfit₁'⟩ :=
    v2_grid_affine_fit 1 hR₀normal h1B₁ hζ (inv_nonneg.mpr hQ₁pos.le) hR₀mass (hJ 0) hHp hζH
      hfit₁
  have hU₁U₀ : U₁ ⊆ U₀ := by
    intro t ht
    obtain ⟨l, hl⟩ := hU₁active ht
    exact hl.2.2
  have hR₀U₁ : R₀ ∩ (univ ×ˢ U₁) = E ∩ (univ ×ˢ U₁) := by
    ext q
    exact ⟨fun hq => ⟨hq.1.1, hq.2⟩, fun hq => ⟨⟨hq.1, mem_univ _, hU₁U₀ hq.2.2⟩, hq.2⟩⟩
  rw [hR₀U₁] at hmass₁ hfloor₁ hfit₁'
  have hU₁T : U₁ ⊆ T := hU₁U₀.trans hU₀T
  have hU₁active' : U₁ ⊆ scalarNormalTimes E := by
    intro t ht
    obtain ⟨l, hl⟩ := hU₁active ht
    exact ⟨l, hl.1⟩
  -- bounds
  have hmassB₂ : ENNReal.ofReal B₂⁻¹ ≤ (ν.prod volume) (E ∩ (univ ×ˢ U₁)) :=
    le_trans (ENNReal.ofReal_le_ofReal (scalarGridStageBound_mass h1B₁ hQ₁)) hmass₁
  have hfloorB₂ : ∀ t ∈ U₁, ENNReal.ofReal B₂⁻¹ ≤ ν {l | (l, t) ∈ E ∩ (univ ×ˢ U₁)} :=
    fun t ht => (ENNReal.ofReal_le_ofReal (scalarGridStageBound_floor h1B₁ hQ₁)).trans
      (hfloor₁ t ht)
  have hcoef₀ : 2624 * B ^ 2 ≤ B₂ := by nlinarith
  have hcoef₁ : 2624 * B₁ ^ 2 ≤ B₂ := by nlinarith
  have hBB₂ : B ≤ B₂ := hBB₁.trans hB₁B₂
  have hsmall i : 0 ≤ (1 / (J i : ℝ)) * p i := mul_nonneg (by positivity) (hp i)
  -- the two component hierarchies
  let G₀ : ScalarGridHierarchy ν E (fun t => F t 0) J hJ p B₂ :=
    { times := U₁
      slope := Fin.cases A₀ (G.comp 0).slope
      intercept := Fin.cases C₀ (G.comp 0).intercept
      measurable_times := hU₁m
      unit_time := hU₁unit
      active_time := hU₁active'
      measurable_slope := fun i => Fin.cases hA₀m (G.comp 0).measurable_slope i
      measurable_intercept := fun i => Fin.cases hC₀m (G.comp 0).measurable_intercept i
      bounded := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro t
          exact ⟨(hb₀ t).1.trans hcoef₀, (hb₀ t).2.trans hcoef₀⟩
        · intro t
          exact ⟨((G.comp 0).bounded j t).1.trans hBB₂, ((G.comp 0).bounded j t).2.trans hBB₂⟩
      mass := hmassB₂
      time_floor := hfloorB₂
      constant_on_grid := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro t ht u hu hcode
          exact hconst₀ t (hU₁U₀ ht) u (hU₁U₀ hu) hcode
        · intro t ht u hu hcode
          exact (G.comp 0).constant_on_grid j t (hU₁T ht) u (hU₁T hu) hcode
      fit := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro q hq
          exact (hfit₀' q ⟨hq.1, mem_univ _, hU₁U₀ hq.2.2⟩).trans (by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef₀ (hsmall 0))
        · intro q hq
          exact ((G.comp 0).fit j q ⟨hq.1, mem_univ _, hU₁T hq.2.2⟩).trans (by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hBB₂ (hsmall j.succ)) }
  have hT1 : (G.comp 1).times = T := G.times_eq
  let G₁ : ScalarGridHierarchy ν E (fun t => F t 1) J hJ p B₂ :=
    { times := U₁
      slope := Fin.cases A₁ (G.comp 1).slope
      intercept := Fin.cases C₁ (G.comp 1).intercept
      measurable_times := hU₁m
      unit_time := hU₁unit
      active_time := hU₁active'
      measurable_slope := fun i => Fin.cases hA₁m (G.comp 1).measurable_slope i
      measurable_intercept := fun i => Fin.cases hC₁m (G.comp 1).measurable_intercept i
      bounded := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro t
          exact ⟨(hb₁ t).1.trans hcoef₁, (hb₁ t).2.trans hcoef₁⟩
        · intro t
          exact ⟨((G.comp 1).bounded j t).1.trans hBB₂, ((G.comp 1).bounded j t).2.trans hBB₂⟩
      mass := hmassB₂
      time_floor := hfloorB₂
      constant_on_grid := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro t ht u hu hcode
          exact hconst₁ t ht u hu hcode
        · intro t ht u hu hcode
          exact (G.comp 1).constant_on_grid j t (hT1 ▸ hU₁T ht) u (hT1 ▸ hU₁T hu) hcode
      fit := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · intro q hq
          exact (hfit₁' q hq).trans (by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef₁ (hsmall 0))
        · intro q hq
          exact ((G.comp 1).fit j q ⟨hq.1, mem_univ _, hT1 ▸ hU₁T hq.2.2⟩).trans (by
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hBB₂ (hsmall j.succ)) }
  let comp : (k : Fin 2) → ScalarGridHierarchy ν E (fun t => F t k) J hJ p B₂ :=
    fun k => match k with
      | ⟨0, _⟩ => G₀
      | ⟨1, _⟩ => G₁
  exact ⟨{ comp := comp, times_eq := rfl }⟩

end V2Hierarchy

/-- **The uniform version-2 hierarchy**: one common subpower bound for a fixed finite list of
lengths. -/
theorem uniform_v2_grid_hierarchy {Λ : Type*} [MeasurableSpace Λ] (hker : LocalFitStatement Λ)
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d < 1) :
    ∀ (n : ℕ) (exponent : Fin n → ℝ), (∀ i, 0 < exponent i) →
    ∃ B : ℕ → ℝ, (∀ k, 1 ≤ B k) ∧ (∀ k, K k ≤ B k) ∧ SubpowerBound N B ∧
      ∀ᶠ k in atTop, ∀ (ν : Measure Λ) [IsProbabilityMeasure ν] (c : Λ → Fin 7 → ℝ)
        (E : Set (Λ × ℝ)) (F : ℝ → Fin 2 → ℝ) (ζ : ℝ) (J : Fin n → ℕ) (hJ : ∀ i, 0 < J i),
        UpperHyp ν c E F (K k) ζ d → 0 < ζ → (K k)⁻¹ ≤ (ν.prod volume).real E →
        (∀ i, 1 / (J i : ℝ) ≤ N k ^ (-exponent i)) →
        (∀ i, ζ ≤ (1 / (J i : ℝ)) ^ 2) →
        Nonempty (V2Hierarchy ν E F J hJ (fun i => N k ^ (-exponent i)) (B k)) := by
  intro n
  induction n with
  | zero =>
      intro exponent hexponent
      let B : ℕ → ℝ := fun k => 8 * K k
      have hB : ∀ k, 1 ≤ B k := fun k => by dsimp [B]; linarith [hK k]
      have hKB : ∀ k, K k ≤ B k := fun k => by dsimp [B]; linarith [hK k]
      have hBsub : SubpowerBound N B :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hK k)) (subpower_const hNt 8) hsub
      refine ⟨B, hB, hKB, hBsub, ?_⟩
      filter_upwards [] with k
      intro ν _ c E F ζ J hJ h hζ hmass hHp hζH
      exact exists_initial_v2_hierarchy ν h.event_measurable h.unit_time
        (hK k) hmass F J hJ (fun i => N k ^ (-exponent i))
  | succ n ih =>
      intro exponent hexponent
      obtain ⟨B, hB, hKB, hBsub, hprevious⟩ :=
        ih (fun i => exponent i.succ) (fun i => hexponent i.succ)
      have h8B : ∀ k, 1 ≤ 8 * B k := fun k => by linarith [hB k]
      have h8Bsub : SubpowerBound N (fun k => 8 * B k) :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hB k)) (subpower_const hNt 8) hBsub
      obtain ⟨Q₀, hQ₀, hQ₀sub, hlocal₀⟩ := uniform_subpower_v2_block_affine_fit
        hker N (fun k => 8 * B k) hN hNt h8B h8Bsub (hexponent 0) hd0 hd
      let B₁ : ℕ → ℝ := fun k => scalarGridStageBound (B k) (Q₀ k)
      have hB₁ : ∀ k, 1 ≤ B₁ k := fun k => (scalarGridStageBound_bounds (hB k) (hQ₀ k)).1
      have hBB₁ : ∀ k, B k ≤ B₁ k := fun k => (scalarGridStageBound_bounds (hB k) (hQ₀ k)).2.1
      have hstagesub : ∀ {X Q : ℕ → ℝ}, (∀ k, 1 ≤ X k) → (∀ k, 1 ≤ Q k) → SubpowerBound N X →
          SubpowerBound N Q → SubpowerBound N (fun k => scalarGridStageBound (X k) (Q k)) := by
        intro X Q hX hQ hXsub hQsub
        exact subpower_mul (fun k => zero_lt_one.trans_le (hN k))
          (fun k => by positivity) (fun k => zero_le_one.trans (hQ k))
          (subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
            (fun k => sq_nonneg (X k)) (subpower_const hNt 10000)
            (subpower_pow hN (fun k => zero_le_one.trans (hX k)) hXsub 2)) hQsub
      have hB₁sub : SubpowerBound N B₁ := hstagesub hB hQ₀ hBsub hQ₀sub
      have h8B₁ : ∀ k, 1 ≤ 8 * B₁ k := fun k => by linarith [hB₁ k]
      have h8B₁sub : SubpowerBound N (fun k => 8 * B₁ k) :=
        subpower_mul (fun k => zero_lt_one.trans_le (hN k)) (fun _ => by norm_num)
          (fun k => zero_le_one.trans (hB₁ k)) (subpower_const hNt 8) hB₁sub
      obtain ⟨Q₁, hQ₁, hQ₁sub, hlocal₁⟩ := uniform_subpower_v2_block_affine_fit
        hker N (fun k => 8 * B₁ k) hN hNt h8B₁ h8B₁sub (hexponent 0) hd0 hd
      let B' : ℕ → ℝ := fun k => scalarGridStageBound (B₁ k) (Q₁ k)
      have hB' : ∀ k, 1 ≤ B' k := fun k => (scalarGridStageBound_bounds (hB₁ k) (hQ₁ k)).1
      have hB₁B' : ∀ k, B₁ k ≤ B' k := fun k => (scalarGridStageBound_bounds (hB₁ k) (hQ₁ k)).2.1
      refine ⟨B', hB', fun k => (hKB k).trans ((hBB₁ k).trans (hB₁B' k)),
        hstagesub hB₁ hQ₁ hB₁sub hQ₁sub, ?_⟩
      filter_upwards [hprevious, hlocal₀, hlocal₁] with k hpreviousk hlocal₀k hlocal₁k
      intro ν _ c E F ζ J hJ h hζ hmass hHp hζH
      obtain ⟨G⟩ := hpreviousk ν c E F ζ (fun i => J i.succ) (fun i => hJ i.succ)
        h hζ hmass (fun i => hHp i.succ) (fun i => hζH i.succ)
      exact V2Hierarchy.extend J hJ (fun i => N k ^ (-exponent i)) G h hζ
        (hKB k) (hB k) (hQ₀ k) (hQ₁ k) (fun i => Real.rpow_nonneg (zero_le_one.trans (hN k)) _)
        (hHp 0) (hζH 0) (hlocal₀k 0) (hlocal₁k 1)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
