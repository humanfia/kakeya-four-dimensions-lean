-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalRefinedEntries, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalRefinedEntries.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalRefinedEntries.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalRefinedEntries.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_scalar_grid_parameter_preparation.StrongPruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalCoarsePalette


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- The actual refined entry remembers its ORIGINAL fine state,
full parameter world, and zoomed cell. -/
def originalRefinedEntry {Ω W B C : Type*} (state : Ω → W) (world : Ω → B)
    (cell : Ω → C) (z : Ω) : W × B × C := (state z,world z,cell z)

/-- One simultaneous restriction gives FINAL floors to every actual
refined entry at every tested width. The cost is charged to old fine-state
weights and the common ORIGINAL coarse velocity palette. The number of
worlds and physical states does not enter the multiplicity. -/
theorem original_refined_entry_selection {Ω σ W B I C : Type*}
    [MeasurableSpace Ω] [Fintype σ]
    [MeasurableSpace W] [MeasurableSingletonClass W]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (state : Ω → W) (hstate : Measurable state) (world : Ω → B) (hworld : Measurable world)
    (cell : σ → Ω → C) (hcell : ∀ i, Measurable (cell i))
    (coarse : B → I) (WF : Finset W) (IF : Finset I)
    (blocks : W × I → Finset B) (cells : σ → W × B → Finset C)
    (P : ℕ) (H : σ → ℕ) (hP : ∀ q, (blocks q).card ≤ P)
    (hH : ∀ i q, (cells i q).card ≤ H i)
    (hw : ∀ z ∈ E, state z ∈ WF) (hi : ∀ z ∈ E, coarse (world z) ∈ IF)
    (hblocks : ∀ z ∈ E, world z ∈ blocks (state z,coarse (world z)))
    (hcells : ∀ i z, z ∈ E → cell i z ∈ cells i (state z,world z))
    (old : W → ENNReal) (palette : σ → I → ENNReal) (δ : σ → ENNReal)
    (hpalette : ∀ i, ∑ a ∈ IF, palette i a ≤ 1) :
    ∃ R : Set Ω, MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ (∑ i, δ i * (P * H i : ℕ)) * ∑ w ∈ WF, old w ∧
      ∀ i z, z ∈ R →
        δ i * old (state z) * palette i (coarse (world z)) <
          (μ.restrict R) ((originalRefinedEntry state world (cell i)) ⁻¹'
            {originalRefinedEntry state world (cell i) z}) := by
  classical
  let T := (i : σ) × (w : WF) × (a : IF) ×
    (b : blocks (w.val,a.val)) × cells i (w.val,b.val)
  let F : T → Set Ω := fun x =>
    {z | state z=x.2.1.val ∧ world z=x.2.2.2.1.val ∧ cell x.1 z=x.2.2.2.2.val}
  let θ : T → ENNReal := fun x => δ x.1 * old x.2.1.val * palette x.1 x.2.2.1.val
  have hF (x : T) : MeasurableSet (F x) :=
    (hstate (measurableSet_singleton _)).inter
      ((hworld (measurableSet_singleton _)).inter (hcell x.1 (measurableSet_singleton _)))
  have hcount (i : σ) (w : WF) (a : IF) :
      Fintype.card ((b : blocks (w.val,a.val)) × cells i (w.val,b.val)) ≤ P*H i := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _b : blocks (w.val,a.val), H i := Finset.sum_le_sum fun b _ => by simpa only [Fintype.card_coe] using hH i (w.val,b.val)
      _ = (blocks (w.val,a.val)).card * H i := by simp
      _ ≤ P*H i := Nat.mul_le_mul_right _ (hP _)
  have hsum : (∑ x : T, θ x) ≤
      (∑ i, δ i * (P * H i : ℕ)) * ∑ w ∈ WF, old w := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ i, ∑ w : WF, ∑ a : IF,
          (P*H i : ℕ) * (δ i * old w.val * palette i a.val) := by
        apply Finset.sum_le_sum
        intro i _
        rw [Fintype.sum_sigma]
        apply Finset.sum_le_sum
        intro w _
        rw [Fintype.sum_sigma]
        apply Finset.sum_le_sum
        intro a _
        change (∑ _x : ((b : blocks (w.val,a.val)) × cells i (w.val,b.val)),
          δ i * old w.val * palette i a.val) ≤ _
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        exact mul_le_mul' (by exact_mod_cast hcount i w a) le_rfl
      _ = ∑ i, (δ i * (P*H i : ℕ)) * (∑ w ∈ WF, old w) * ∑ a ∈ IF, palette i a := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ w : WF, ∑ a : IF,
              ((δ i * (P*H i : ℕ)) * old w.val) * palette i a.val := by
            apply Finset.sum_congr rfl
            intro w _
            apply Finset.sum_congr rfl
            intro a _
            ring
          _ = ∑ w : WF, ((δ i * (P*H i : ℕ)) * old w.val) *
              (∑ a : IF, palette i a.val) := by simp_rw [← Finset.mul_sum]
          _ = (∑ w : WF, (δ i * (P*H i : ℕ)) * old w.val) *
              (∑ a : IF, palette i a.val) := (Finset.sum_mul _ _ _).symm
          _ = ((δ i * (P*H i : ℕ)) * ∑ w : WF, old w.val) *
              (∑ a : IF, palette i a.val) := by rw [← Finset.mul_sum]
          _ = _ := by rw [Finset.sum_coe_sort WF old,Finset.sum_coe_sort IF (palette i)]
      _ ≤ ∑ i, (δ i * (P*H i : ℕ)) * ∑ w ∈ WF, old w := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right (by positivity) (hpalette i)
      _ = _ := (Finset.sum_mul _ _ _).symm
  obtain ⟨R,hR,hsub,hloss,hfloor⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_measurable_current_floor_pruning
      μ F θ hF hE
  refine ⟨R,hR,hsub,hloss.trans hsum,?_⟩
  intro i z hz
  have hzE := hsub hz
  let x : T := ⟨i,⟨state z,hw z hzE⟩,⟨coarse (world z),hi z hzE⟩,
    ⟨world z,hblocks z hzE⟩,⟨cell i z,hcells i z hzE⟩⟩
  have hzF : z ∈ R ∩ F x := ⟨hz,rfl,rfl,rfl⟩
  rcases hfloor x with hempty | hf
  · rw [hempty] at hzF
    exact hzF.elim
  · have heq : R ∩ F x =
        (originalRefinedEntry state world (cell i)) ⁻¹' {originalRefinedEntry state world (cell i) z} ∩ R := by
      ext y
      simp only [F,x,mem_inter_iff,mem_ofPred_eq,mem_preimage,mem_singleton_iff,
        originalRefinedEntry,Prod.mk.injEq]
      tauto
    rw [Measure.restrict_apply (show MeasurableSet
      ((originalRefinedEntry state world (cell i)) ⁻¹' {originalRefinedEntry state world (cell i) z}) from
        (hstate.prodMk (hworld.prodMk (hcell i))) (measurableSet_singleton _))]
    rw [heq] at hf
    exact hf

/-- The literal final refined-entry law inherits the old fine-state
joint ceiling, then its genuine original reference floor supplies the
common original coarse-bin palette. No witness law is an extra input. -/
theorem original_refined_entry_posterior {Ω W B C V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSingletonClass W]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C] [MeasurableSpace V]
    (μ : Measure Ω) (R : Set Ω) (hR : MeasurableSet R)
    (state : Ω → W) (hstate : Measurable state) (world : Ω → B) (hworld : Measurable world)
    (cell : Ω → C) (hcell : Measurable cell) (control : Ω → V) (hv : Measurable control)
    (π : Measure V) [IsProbabilityMeasure π] (coarseBin : B → Set V)
    (hbin : ∀ b, MeasurableSet (coarseBin b))
    (hknown : ∀ y ∈ R, control y ∈ coarseBin (world y))
    (old : W → ENNReal) (K δ : ENNReal) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hcap : ∀ w (A : Set V), MeasurableSet A →
      μ {y | state y=w ∧ control y∈A} ≤ K * old w * π A)
    (z : Ω) (_hz : z ∈ R)
    (hfloor : δ * old (state z) * π (coarseBin (world z)) <
      (μ.restrict R) ((originalRefinedEntry state world cell) ⁻¹'
        {originalRefinedEntry state world cell z})) :
    ∀ A : Set V, MeasurableSet A →
      (μ.restrict R) {y | originalRefinedEntry state world cell y =
        originalRefinedEntry state world cell z ∧ control y∈A} ≤
        (K/δ) * (μ.restrict R) ((originalRefinedEntry state world cell) ⁻¹'
          {originalRefinedEntry state world cell z}) * (originalBinPalette π (coarseBin (world z))) A := by
  let entry := originalRefinedEntry state world cell
  have he : Measurable entry := hstate.prodMk (hworld.prodMk hcell)
  let ν := (μ.restrict R).restrict (entry ⁻¹' {entry z})
  have hmass : ν univ = (μ.restrict R) (entry ⁻¹' {entry z}) := Measure.restrict_apply_univ _
  have hpositive : ν univ ≠ 0 := by
    rw [hmass]
    exact ne_of_gt (lt_of_le_of_lt bot_le hfloor)
  have hentry : ∀ᵐ y ∂ν, entry y=entry z ∧ y∈R := by
    filter_upwards [ae_restrict_mem (he (measurableSet_singleton _)),
      (ae_restrict_mem hR).filter_mono (ae_mono Measure.restrict_le_self)] with y hy hRy
    exact ⟨hy,hRy⟩
  have hfull : ∀ᵐ y ∂ν, control y∈coarseBin (world z) := by
    filter_upwards [hentry] with y hy
    have hw : world y=world z := congrArg (fun q : W × B × C => q.2.1) hy.1
    simpa only [hw] using hknown y hy.2
  have hcaps (A : Set V) (hA : MeasurableSet A) :
      ν (control ⁻¹' A) ≤ K * old (state z) * π A := by
    calc
      _ = (μ.restrict R) ((control ⁻¹' A) ∩ (entry ⁻¹' {entry z})) :=
        Measure.restrict_apply (hv hA)
      _ ≤ μ {y | state y=state z ∧ control y∈A} := by
        apply le_trans (Measure.restrict_le_self _)
        apply measure_mono
        intro y hy
        refine ⟨?_,hy.1⟩
        exact congrArg (fun q : W × B × C => q.1) hy.2
      _ ≤ _ := hcap _ A hA
  have hh := positive_entry_original_bin_cap ν π control (coarseBin (world z)) (hbin _)
    (old (state z)) K δ hδ0 hδtop hpositive hfull (by rw [hmass]; exact hfloor.le) hcaps
  intro A hA
  have heq : ν (control ⁻¹' A) =
      (μ.restrict R) {y | entry y=entry z ∧ control y∈A} := by
    rw [Measure.restrict_apply (hv hA)]
    congr 1
    ext y
    simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq,and_comm]
  have hhA := hh A hA
  rw [hmass,heq] at hhA
  exact hhA

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
