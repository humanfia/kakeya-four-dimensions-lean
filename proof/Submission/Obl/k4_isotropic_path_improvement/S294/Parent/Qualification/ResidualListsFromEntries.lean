-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ResidualListsFromEntries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ResidualListsFromEntries.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ResidualListsFromEntries.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ResidualListsFromEntries.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalEntryPaletteCount
import Submission.Obl.k4_scalar_heavy_intercept_selection.PositiveCodes
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound
import Submission.Lib.K4QuadraticSheets.JetBins


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Remove the velocity condition from actual residual lists using
the SAME original entry laws and their COMMON original palette.
Every witness law is the literal restriction of the supplied original
measure to the witness's entry. No auxiliary law is assumed. -/
theorem residual_lists_from_original_entries {Ω J Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace J] [MeasurableSingletonClass J]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) [IsFiniteMeasure μ] (π : Q → Measure V) [∀ q, IsProbabilityMeasure (π q)]
    (entry : Ω → J) (he : Measurable entry) (velocity : Ω → V) (hv : Measurable velocity)
    (cell : Ω → Q) (residual : Ω → ℝ) (s K M : ℝ) (hs : 0 < s) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (original selected : Set Ω) (hfull : ∀ᵐ z ∂μ, z ∈ original) (hsub : selected ⊆ original)
    (table : Q × V → Finset ℤ) (hcard : ∀ q, ((table q).card : ℝ) ≤ M)
    (hknown : ∀ z ∈ original, ⌊residual z / s⌋ ∈ table (cell z,velocity z))
    (hcell : ∀ z ∈ original, ∀ z' ∈ original, entry z = entry z' → cell z = cell z')
    (hosc : ∀ z ∈ original, ∀ z' ∈ original, entry z = entry z' → |residual z - residual z'| ≤ s)
    (hpositive : ∀ z ∈ selected, μ (entry ⁻¹' {entry z}) ≠ 0)
    (hcap : ∀ z ∈ selected, ∀ A : Set V, MeasurableSet A →
      μ {y | entry y = entry z ∧ velocity y ∈ A} ≤
        ENNReal.ofReal K * μ (entry ⁻¹' {entry z}) * (π (cell z)) A) :
    ∃ lists : Q → Finset ℤ, (∀ q, ((lists q).card : ℝ) ≤ 3 * M * K) ∧
      ∀ z ∈ selected, ⌊residual z / s⌋ ∈ lists (cell z) := by
  classical
  let Codes : Q → Set ℤ := fun q =>
    {n | ∃ z ∈ selected, cell z = q ∧ ⌊residual z / s⌋ = n}
  have hcount (q : Q) (N : Finset ℤ) (hN : (↑N : Set ℤ) ⊆ Codes q) :
      (N.card : ℝ) ≤ 3 * M * K := by
    have hex (n : N) : ∃ z ∈ selected, cell z = q ∧ ⌊residual z / s⌋ = n.val := hN n.property
    choose point hp using hex
    let laws : N → Measure Ω := fun n => μ.restrict (entry ⁻¹' {entry (point n)})
    haveI : ∀ n : N, IsFiniteMeasure (laws n) := fun n => by dsimp [laws]; infer_instance
    have hpos (n : N) (_hn : n ∈ (Finset.univ : Finset N)) : laws n univ ≠ 0 := by
      simpa only [laws,Measure.restrict_apply_univ] using hpositive (point n) (hp n).1
    have hcaps (n : N) (_hn : n ∈ (Finset.univ : Finset N)) (A : Set V) (hA : MeasurableSet A) :
        laws n (velocity ⁻¹' A) ≤ ENNReal.ofReal K * laws n univ * (π q) A := by
      simp only [laws,Measure.restrict_apply (hv hA),Measure.restrict_apply_univ]
      have heq : (velocity ⁻¹' A) ∩ (entry ⁻¹' {entry (point n)}) =
          {z | entry z = entry (point n) ∧ velocity z ∈ A} := by
        ext z
        simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq,and_comm]
      rw [heq]
      have hh := hcap (point n) (hp n).1 A hA
      simpa only [(hp n).2.1] using hh
    have hlists (v : V) :
        (((Finset.univ : Finset N).filter fun n => laws n (velocity ⁻¹' {v}) ≠ 0).card : ENNReal) ≤
          ENNReal.ofReal (3 * M) := by
      let T := (Finset.univ : Finset N).filter fun n => laws n (velocity ⁻¹' {v}) ≠ 0
      let near := (table (q,v)).biUnion fun k => ({k-1,k,k+1} : Finset ℤ)
      have hnear : (near.card : ℝ) ≤ 3 * M := by
        calc
          (near.card : ℝ) ≤ ∑ k ∈ table (q,v), (({k-1,k,k+1} : Finset ℤ).card : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
          _ ≤ ∑ _k ∈ table (q,v), (3 : ℝ) := Finset.sum_le_sum fun k _ => by
            exact_mod_cast (Finset.card_le_three : ({k-1,k,k+1} : Finset ℤ).card ≤ 3)
          _ = 3 * ((table (q,v)).card : ℝ) := by simp; ring
          _ ≤ 3 * M := mul_le_mul_of_nonneg_left (hcard (q,v)) (by norm_num)
      have himage : T.image (fun n : N => n.val) ⊆ near := by
        intro k hk
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
        have hnonzero := (Finset.mem_filter.mp hn).2
        have hgood : ∀ᵐ z ∂laws n, z ∈ original ∧ entry z = entry (point n) := by
          filter_upwards [ae_mono Measure.restrict_le_self hfull,
            ae_restrict_mem (he (measurableSet_singleton (entry (point n))))] with z hz hez
          exact ⟨hz,hez⟩
        obtain ⟨z,hz,hzv⟩ :=
          Submission.Obl.k4_scalar_heavy_intercept_selection.exists_good_in_positive_code
            (laws n) velocity v hnonzero _ hgood
        have hzcell : cell z = q := (hcell z hz.1 (point n) (hsub (hp n).1) hz.2).trans (hp n).2.1
        have hbin := hknown z hz.1
        rw [hzcell,hzv] at hbin
        have hclose := hosc (point n) (hsub (hp n).1) z hz.1 hz.2.symm
        have hf := Submission.Lib.K4QuadraticSheets.floor_sub_le_one_of_abs_le hs hclose
        rw [(hp n).2.2] at hf
        have hmember : n.val ∈ ({⌊residual z / s⌋-1,⌊residual z / s⌋,⌊residual z / s⌋+1} : Finset ℤ) := by
          simp only [Finset.mem_insert,Finset.mem_singleton]
          have hh := abs_le.mp hf
          omega
        exact Finset.mem_biUnion.mpr ⟨_,hbin,hmember⟩
      have hT : (T.card : ℝ) ≤ 3 * M := by
        calc
          (T.card : ℝ) = ((T.image (fun n : N => n.val)).card : ℝ) := by
            rw [Finset.card_image_of_injective _ Subtype.val_injective]
          _ ≤ (near.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card himage)
          _ ≤ 3 * M := hnear
      have hh := ENNReal.ofReal_le_ofReal hT
      simpa only [ENNReal.ofReal_natCast] using hh
    have hENN := original_entry_palette_count (π q) laws velocity hv Finset.univ
      (ENNReal.ofReal K) (ENNReal.ofReal (3*M)) hpos hcaps hlists
    have hr := ENNReal.toReal_mono (by finiteness) hENN
    have hreal : (N.card : ℝ) ≤ K * (3*M) := by
      simpa only [Finset.card_univ,Fintype.card_coe,ENNReal.toReal_natCast,ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hK,ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hM)] using hr
    exact hreal.trans_eq (by ring)
  have hfinite (q : Q) :=
    Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
      (Codes q) (3*M*K) (hcount q)
  refine ⟨fun q => (hfinite q).toFinset,?_,?_⟩
  · intro q
    exact hcount q _ (by simp)
  · intro z hz
    exact (hfinite (cell z)).mem_toFinset.mpr ⟨z,hz,rfl,rfl⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
