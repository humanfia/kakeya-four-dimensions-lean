-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.WorldResidualSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/WorldResidualSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/WorldResidualSelection.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/WorldResidualSelection.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ResidualListsFromEntries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomResidualSelection


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

def originalResidualValue {Ω : Type*} (c : Ω → Fin 7 → ℝ)
    (row : Ω → Fin 2 → ℝ) (time : Ω → ℝ) (z : Ω) : ℝ :=
  zR (fun _ => row z) (c z) (time z)

def originalResidualCell {Ω W : Type*} (world : Ω → W) (c : Ω → Fin 7 → ℝ)
    (time : Ω → ℝ) (s : ℝ) (z : Ω) : W × (Fin 4 → ℤ) :=
  (world z,Submission.Lib.K4CommonLocalChoice.cell s (zpos (c z) (time z)))

/-- Worldwise mass floors add with no number-of-worlds factor.
The partition is the actual measurable original world map. -/
theorem original_mass_of_worldwise_bounds {Ω W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    (μ : Measure Ω) (world : Ω → W) (hw : Measurable world)
    (E S : Set Ω) (hE : MeasurableSet E) (hS : MeasurableSet S) (D : ENNReal)
    (hbound : ∀ w, μ (E ∩ world ⁻¹' {w}) ≤ D * μ (S ∩ world ⁻¹' {w})) :
    μ E ≤ D*μ S := by
  have hsum (A : Set Ω) (hA : MeasurableSet A) :
      μ A = ∑' w : W, μ (A ∩ world ⁻¹' {w}) := by
    have hcover : (⋃ w : W, A ∩ world ⁻¹' {w}) = A := by
      ext z
      simp only [mem_iUnion,mem_inter_iff,mem_preimage,mem_singleton_iff]
      constructor
      · rintro ⟨w,hz,_⟩; exact hz
      · intro hz; exact ⟨world z,hz,rfl⟩
    calc
      μ A = μ (⋃ w : W, A ∩ world ⁻¹' {w}) := congrArg μ hcover.symm
      _ = _ := by
        apply measure_iUnion
        · intro w w' hww'
          apply disjoint_left.mpr
          rintro z ⟨_,hzw⟩ ⟨_,hzw'⟩
          exact hww' (hzw.symm.trans hzw')
        · intro w
          exact hA.inter (hw (measurableSet_singleton w))
  rw [hsum E hE,hsum S hS,← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hbound

/-- Actual old entry laws produce all local residual lists and hence
ResC on a dense restriction, separately in EVERY original world.
The mass factor has no number-of-worlds term. Palettes can vary with
the world/cell but remain common to every entry counted in that cell. -/
theorem original_world_residual_preparation {Ω W : Type*} {J V : ℕ → Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    [∀ i, MeasurableSpace (J i)] [∀ i, MeasurableSingletonClass (J i)]
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ : Measure Ω) [IsFiniteMeasure μ] (world : Ω → W) (hw : Measurable world)
    (c : Ω → Fin 7 → ℝ) (hc : Measurable c) (row : Ω → Fin 2 → ℝ) (hrow : Measurable row)
    (time : Ω → ℝ) (ht : Measurable time)
    (original selected : Set Ω) (hselected : MeasurableSet selected)
    (hfull : ∀ᵐ z ∂μ, z ∈ original) (hsub : selected ⊆ original)
    (K : ℝ) (hK : 1 ≤ K) (htime : ∀ z ∈ selected, time z ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ selected, ∀ i, |c z i| ≤ K) (hrowBound : ∀ z ∈ selected, ‖row z‖ ≤ K)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (A ζ : ℝ) (hA : 1 ≤ A)
    (hs0 : s 0 = 1) (hspos : ∀ i, 0 < s i)
    (hratio : ∀ i, i+1 < L → s i ≤ A * s (i+1)) (hfloor : s (L-1) ≤ ζ)
    (entry : (i : ℕ) → Ω → J i) (he : ∀ i, Measurable (entry i))
    (velocity : (i : ℕ) → Ω → V i) (hv : ∀ i, Measurable (velocity i))
    (π : (i : ℕ) → W × (Fin 4 → ℤ) → Measure (V i))
    [∀ i q, IsProbabilityMeasure (π i q)] (palK palM : ℕ → ℝ)
    (hpalK : ∀ i < L, 0 ≤ palK i) (hpalM : ∀ i < L, 0 ≤ palM i)
    (table : (i : ℕ) → (W × (Fin 4 → ℤ)) × V i → Finset ℤ)
    (hcard : ∀ i < L, ∀ q, ((table i q).card : ℝ) ≤ palM i)
    (hknown : ∀ i < L, ∀ z ∈ original,
      ⌊originalResidualValue c row time z / s i⌋ ∈
        table i (originalResidualCell world c time (s i) z,velocity i z))
    (hcell : ∀ i < L, ∀ z ∈ original, ∀ z' ∈ original, entry i z = entry i z' →
      originalResidualCell world c time (s i) z = originalResidualCell world c time (s i) z')
    (hosc : ∀ i < L, ∀ z ∈ original, ∀ z' ∈ original, entry i z = entry i z' →
      |originalResidualValue c row time z - originalResidualValue c row time z'| ≤ s i)
    (hpositive : ∀ i < L, ∀ z ∈ selected, μ ((entry i) ⁻¹' {entry i z}) ≠ 0)
    (hcap : ∀ i < L, ∀ z ∈ selected, ∀ B : Set (V i), MeasurableSet B →
      μ {y | entry i y = entry i z ∧ velocity i y ∈ B} ≤
        ENNReal.ofReal (palK i) * μ ((entry i) ⁻¹' {entry i z}) *
          (π i (originalResidualCell world c time (s i) z)) B) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ selected ∧
      (∀ w, μ (selected ∩ world ⁻¹' {w}) ≤
        (∏ i ∈ Finset.range L, ((4 : ENNReal) ^ 4 * (⌈3 * palM i * palK i⌉₊ + 1 : ℕ))) *
          μ (E ∩ world ⁻¹' {w})) ∧
      ∀ z ∈ E, ∀ z' ∈ E, world z = world z' →
        |originalResidualValue c row time z - originalResidualValue c row time z'| ≤
          2 * (A + 5 * K ^ 2) * (‖zpos (c z) (time z) - zpos (c z') (time z')‖ + ζ) := by
  classical
  let Z : Ω → Fin 4 → ℝ := fun z => zpos (c z) (time z)
  let R : Ω → ℝ := originalResidualValue c row time
  let Y : Ω → Fin 1 → ℝ := fun z _ => R z
  have hZ : Measurable Z := by
    unfold Z zpos zx zy
    fun_prop
  have hR : Measurable R := by
    unfold R originalResidualValue zR zv
    simp only [dotProduct,Fin.sum_univ_two]
    fun_prop
  have hY : Measurable Y := measurable_pi_iff.mpr fun _ => hR
  have hYbound : ∀ z ∈ selected, ‖Y z‖ ≤ 5 * K ^ 2 := by
    intro z hz
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro _
    exact residual_bound_of_original_coefficients (c z) (fun _ => row z) (time z) K hK
      (htime z hz) (hcoeff z hz) (hrowBound z hz)
  let counts : ℕ → ℕ := fun i => ⌈3 * palM i * palK i⌉₊ + 1
  have hlocal (i : ℕ) (hi : i < L) :
      ∃ lists : W × (Fin 4 → ℤ) → Finset ℤ,
        (∀ q, (lists q).card ≤ counts i) ∧
        ∀ z ∈ selected, ⌊R z / s i⌋ ∈ lists (originalResidualCell world c time (s i) z) := by
    obtain ⟨lists,hsize,hmem⟩ := residual_lists_from_original_entries μ (π i) (entry i) (he i)
      (velocity i) (hv i) (originalResidualCell world c time (s i)) R (s i) (palK i) (palM i)
      (hspos i) (hpalK i hi) (hpalM i hi) original selected hfull hsub (table i)
      (hcard i hi) (hknown i hi) (hcell i hi) (hosc i hi) (hpositive i hi) (hcap i hi)
    refine ⟨lists,?_,hmem⟩
    intro q
    have hh := (hsize q).trans (Nat.le_ceil (3 * palM i * palK i))
    have hc : (lists q).card ≤ ⌈3 * palM i * palK i⌉₊ := by exact_mod_cast hh
    exact hc.trans (Nat.le_succ _)
  have hlist : ∀ i < L, ∀ (w : W) (n : Fin 4 → ℤ),
      ∃ S : Finset (Fin 1 → ℤ), S.card ≤ counts i ∧
        ∀ z ∈ selected, world z = w → Submission.Lib.K4CommonLocalChoice.cell (s i) (Z z) = n →
          Submission.Lib.K4CommonLocalChoice.cell (s i) (Y z) ∈ S := by
    intro i hi w n
    obtain ⟨lists,hsize,hmem⟩ := hlocal i hi
    refine ⟨(lists (w,n)).image (fun k => fun _ : Fin 1 => k),
      Finset.card_image_le.trans (hsize (w,n)),?_⟩
    intro z hz hwz hn
    have hm := hmem z hz
    change ⌊R z / s i⌋ ∈ lists (world z,Submission.Lib.K4CommonLocalChoice.cell (s i) (Z z)) at hm
    rw [hwz,hn] at hm
    exact Finset.mem_image.mpr ⟨_,hm,rfl⟩
  obtain ⟨E,_,hE,hEsub,_,hmass,hcmp⟩ :=
    Submission.Lib.K4CommonLocalChoice.common_local_choice μ world hw Z hZ Y hY selected hselected
      (5 * K ^ 2) (by positivity) hYbound L hL s counts A hA hs0 hspos hratio hlist
  refine ⟨E,hE,hEsub,hmass,?_⟩
  intro z hz z' hz' hwz
  have hh := hcmp z hz z' hz' hwz
  have hvalue : |R z - R z'| ≤ ‖Y z - Y z'‖ := norm_le_pi_norm (Y z - Y z') (0 : Fin 1)
  exact hvalue.trans (hh.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hfloor) (by positivity)))

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
