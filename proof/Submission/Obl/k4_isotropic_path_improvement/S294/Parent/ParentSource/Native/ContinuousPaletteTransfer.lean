-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.ContinuousPaletteTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/ContinuousPaletteTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/ContinuousPaletteTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/ContinuousPaletteTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/ContinuousPaletteTransfer.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteTransfer

/-! Implement the finite palette change as an actual measurable selection
of the original probability space, without changing its reference marginals. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped BigOperators

theorem finite_cell_real_sum {Ω I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [Fintype I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (f : Ω → I) (hf : Measurable f) :
    (∑ i, μ.real {x | x ∈ S ∧ f x = i}) = μ.real S := by
  classical
  have hcell (i : I) : (μ.restrict S).real (f ⁻¹' {i}) = μ.real {x | x ∈ S ∧ f x = i} := by
    have heq : f ⁻¹' {i} ∩ S = {x | x ∈ S ∧ f x = i} := by ext x; simp [and_comm]
    rw [measureReal_def, Measure.restrict_apply (hf (measurableSet_singleton i)), heq]
    rfl
  calc
    _ = ∑ i, (μ.restrict S).real (f ⁻¹' {i}) :=
      Finset.sum_congr rfl (fun i _ => (hcell i).symm)
    _ = (μ.restrict S).real univ := by
      simpa only [Finset.coe_univ, preimage_univ] using
        sum_measureReal_preimage_singleton (μ := μ.restrict S) Finset.univ
          (fun i _ => hf (measurableSet_singleton i))
    _ = _ := by simp [measureReal_def]

theorem finite_triple_real_sum {Ω E Z Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    [MeasurableSpace Z] [Fintype Z] [MeasurableSingletonClass Z]
    [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω)
    (f : Ω → E) (z : Ω → Z) (y : Ω → Y)
    (hf : Measurable f) (hz : Measurable z) (hy : Measurable y) :
    (∑ e, ∑ a, ∑ b, μ.real {x | x ∈ S ∧ f x = e ∧ z x = a ∧ y x = b}) = μ.real S := by
  have h := finite_cell_real_sum μ S (fun x => (f x, z x, y x)) (hf.prodMk (hz.prodMk hy))
  simpa only [Fintype.sum_prod_type, Prod.mk.injEq] using h

def paletteStateCut {Ω Z Y : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (z : Ω → Z) (y : Ω → Y) (ε : ℝ) : Set Ω :=
  {x | x ∈ S ∧ ε * μ.real {t | z t = z x} ≤ μ.real {t | z t = z x ∧ y t = y x}}

theorem measurableSet_paletteStateCut {Ω Z Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Fintype Z] [MeasurableSingletonClass Z]
    [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) (S : Set Ω) (hS : MeasurableSet S)
    (z : Ω → Z) (y : Ω → Y) (hz : Measurable z) (hy : Measurable y) (ε : ℝ) :
    MeasurableSet (paletteStateCut μ S z y ε) := by
  exact hS.inter (measurableSet_le
    (measurable_const.mul ((measurable_of_countable (fun a : Z => μ.real {t | z t = a})).comp hz))
    ((measurable_of_countable (fun p : Z × Y => μ.real {t | z t = p.1 ∧ y t = p.2})).comp
      (hz.prodMk hy)))

theorem paletteStateCut_atom_eq {Ω E Z Y : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (f : Ω → E) (z : Ω → Z) (y : Ω → Y)
    (ε : ℝ) (e : E) (a : Z) (b : Y) :
    μ.real {x | x ∈ paletteStateCut μ S z y ε ∧ f x = e ∧ z x = a ∧ y x = b} =
      paletteRefinementRetained
        (fun e a b => μ.real {x | x ∈ S ∧ f x = e ∧ z x = a ∧ y x = b})
        (fun a b => μ.real {x | z x = a ∧ y x = b})
        (fun a => μ.real {x | z x = a}) ε e a b := by
  classical
  have heq : {x | x ∈ paletteStateCut μ S z y ε ∧ f x = e ∧ z x = a ∧ y x = b} =
      if ε * μ.real {t | z t = a} ≤ μ.real {t | z t = a ∧ y t = b}
      then {x | x ∈ S ∧ f x = e ∧ z x = a ∧ y x = b} else ∅ := by
    ext x
    by_cases hza : z x = a <;> by_cases hyb : y x = b <;>
      simp [paletteStateCut, hza, hyb, and_assoc]
  rw [heq, paletteRefinementRetained]
  split_ifs <;> simp

/-- The palette ambiguity cut is an actual measurable subset of the ORIGINAL
probability space. Its cost is `ε*K`, and every new-palette/fine-state cell is
capped using the old fine-state mass and old new-palette marginal. -/
theorem continuous_palette_refinement {Ω E Z Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    [MeasurableSpace Z] [Fintype Z] [MeasurableSingletonClass Z]
    [MeasurableSpace Y] [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (f : Ω → E) (z : Ω → Z) (y : Ω → Y)
    (hf : Measurable f) (hz : Measurable z) (hy : Measurable y)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (K : ℕ)
    (hK : ∀ a, (Finset.univ.filter (fun b => 0 < μ.real {x | z x = a ∧ y x = b})).card ≤ K)
    (hOld : ∀ e a, μ.real {x | x ∈ S ∧ f x = e ∧ z x = a} ≤
      R * μ.real {x | f x = e} * μ.real {x | z x = a}) :
    MeasurableSet (paletteStateCut μ S z y ε) ∧
    paletteStateCut μ S z y ε ⊆ S ∧
    μ.real (S \ paletteStateCut μ S z y ε) ≤ ε * (K : ℝ) ∧
    ∀ e b, μ.real {x | x ∈ paletteStateCut μ S z y ε ∧ f x = e ∧ y x = b} ≤
      (R / ε) * μ.real {x | f x = e} * μ.real {x | y x = b} := by
  classical
  let G := paletteStateCut μ S z y ε
  let T : E → Z → Y → ℝ := fun e a b => μ.real {x | x ∈ S ∧ f x = e ∧ z x = a ∧ y x = b}
  let π : Z → Y → ℝ := fun a b => μ.real {x | z x = a ∧ y x = b}
  let πZ : Z → ℝ := fun a => μ.real {x | z x = a}
  let w : E → ℝ := fun e => μ.real {x | f x = e}
  have hG : MeasurableSet G := measurableSet_paletteStateCut μ S hS z y hz hy ε
  have hsub : G ⊆ S := fun x hx => hx.1
  have hRet (e : E) (a : Z) (b : Y) :
      μ.real {x | x ∈ G ∧ f x = e ∧ z x = a ∧ y x = b} =
        paletteRefinementRetained T π πZ ε e a b := paletteStateCut_atom_eq μ S f z y ε e a b
  have hOld₃ (e : E) (a : Z) (b : Y) : T e a b ≤ R * w e * πZ a := by
    have hle : T e a b ≤ μ.real {x | x ∈ S ∧ f x = e ∧ z x = a} := by
      apply measureReal_mono
      · intro x hx
        exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
      · exact measure_ne_top μ _
    exact hle.trans (hOld e a)
  have hmarginal (a : Z) (b : Y) : (∑ e, T e a b) ≤ π a b := by
    have hsum : (∑ e, T e a b) = μ.real {x | x ∈ S ∧ z x = a ∧ y x = b} := by
      convert finite_cell_real_sum μ {x | x ∈ S ∧ z x = a ∧ y x = b} f hf using 1
      apply Finset.sum_congr rfl
      intro e _
      dsimp [T]
      apply congrArg μ.real
      ext x
      simp [and_assoc, and_comm, and_left_comm]
    rw [hsum]
    exact measureReal_mono (fun x hx => hx.2)
  have hsumT : (∑ e, ∑ a, ∑ b, T e a b) = μ.real S :=
    finite_triple_real_sum μ S f z y hf hz hy
  have hsumG : (∑ e, ∑ a, ∑ b, paletteRefinementRetained T π πZ ε e a b) = μ.real G := by
    simpa only [hRet] using finite_triple_real_sum μ G f z y hf hz hy
  have hsumZ : (∑ a, πZ a) = 1 := by
    simpa only [πZ, mem_univ, true_and, measureReal_def, measure_univ, ENNReal.toReal_one] using
      finite_cell_real_sum μ univ z hz
  have hlost := paletteRefinement_lost_mass T π πZ hε
    (fun _ => measureReal_nonneg) hmarginal K hK
  simp only [Finset.sum_sub_distrib, hsumT, hsumG, hsumZ, mul_one] at hlost
  have hdecomp : μ.real (S \ G) + μ.real G = μ.real S := by
    have h := measure_sdiff_add_inter (μ := μ) S hG
    rw [Set.inter_eq_right.mpr hsub] at h
    simp only [measureReal_def]
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), h]
  refine ⟨hG, hsub, by linarith, ?_⟩
  intro e b
  have hcap := paletteRefinement_joint_cap T π πZ w hε hR
    (fun _ => measureReal_nonneg) (fun _ _ => measureReal_nonneg) hOld₃ e b
  have hnew : (∑ a, paletteRefinementRetained T π πZ ε e a b) =
      μ.real {x | x ∈ G ∧ f x = e ∧ y x = b} := by
    rw [← finite_cell_real_sum μ {x | x ∈ G ∧ f x = e ∧ y x = b} z hz]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hRet]
    congr 1
    ext x
    simp [and_assoc, and_comm, and_left_comm]
  have hπY : (∑ a, π a b) = μ.real {x | y x = b} := by
    convert finite_cell_real_sum μ {x | y x = b} z hz using 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [π]
    apply congrArg μ.real
    ext x
    simp [and_comm]
  rw [hnew, hπY] at hcap
  exact hcap

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
