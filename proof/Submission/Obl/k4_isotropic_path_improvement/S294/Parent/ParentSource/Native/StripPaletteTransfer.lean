-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPaletteTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPaletteTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPaletteTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPaletteTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPaletteTransfer.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePaletteTransfer
import Submission.Lib.K4VelocityStrips

/-! A fine state's normalized-palette concentration makes its predicted
strip heavy under the SAME original coarse velocity palette. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped BigOperators RealInnerProductSpace

theorem finite_palette_event_sum {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (z : Ω → Z) (hz : Measurable z)
    (B : Finset Z) :
    (∑ b ∈ B, μ.real {x | x ∈ S ∧ z x = b}) = μ.real {x | x ∈ S ∧ z x ∈ B} := by
  classical
  have hcell (b : Z) : (μ.restrict S).real (z ⁻¹' {b}) = μ.real {x | x ∈ S ∧ z x = b} := by
    simp only [measureReal_def, Measure.restrict_apply (hz (measurableSet_singleton b))]
    apply congrArg (fun D : Set Ω => (μ D).toReal)
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    tauto
  calc
    _ = ∑ b ∈ B, (μ.restrict S).real (z ⁻¹' {b}) := Finset.sum_congr rfl (fun b _ => (hcell b).symm)
    _ = (μ.restrict S).real (z ⁻¹' (B : Set Z)) :=
      sum_measureReal_preimage_singleton B (fun b _ => hz (measurableSet_singleton b))
    _ = _ := by
      rw [measureReal_def, Measure.restrict_apply (hz B.finite_toSet.measurableSet)]
      apply congrArg (fun D : Set Ω => (μ D).toReal)
      ext x
      simp only [mem_inter_iff, mem_preimage, Finset.mem_coe, mem_ofPred_eq]
      tauto

theorem fine_palette_event_joint_cap {Ω E Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) [IsFiniteMeasure μ] (G : Set Ω) (f : Ω → E) (z : Ω → Z)
    (hz : Measurable z) (A : ℝ) (e : E)
    (hcap : ∀ b, μ.real {x | x ∈ G ∧ f x = e ∧ z x = b} ≤
      A * μ.real {x | f x = e} * μ.real {x | z x = b}) (B : Finset Z) :
    μ.real {x | x ∈ G ∧ f x = e ∧ z x ∈ B} ≤
      A * μ.real {x | f x = e} * μ.real {x | z x ∈ B} := by
  have hG := finite_palette_event_sum μ (G ∩ {x | f x = e}) z hz B
  simp only [mem_inter_iff, mem_ofPred_eq, and_assoc] at hG
  have hZ := finite_palette_event_sum μ univ z hz B
  simp only [mem_univ, true_and] at hZ
  rw [← hG, ← hZ, Finset.mul_sum]
  exact Finset.sum_le_sum (fun b _ => hcap b)

/-- Equal bins thicken a predicted strip by at most twice the bin width. -/
theorem affineStrip_of_same_velocity_palette {a r β : ℝ} (ha : 0 < a)
    {n x y : StripSpace} (hn : ‖n‖ = 1)
    (hbin : velocityPalette a x = velocityPalette a y) (hy : y ∈ affineStrip n β r) :
    x ∈ affineStrip n β (r + 2 * a) := by
  have hd := velocityPalette_norm_sub_le ha hbin
  have hi : |inner ℝ x n - inner ℝ y n| ≤ 2 * a := by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans (by simpa only [hn, mul_one] using hd)
  have hs : |inner ℝ x n - β| ≤ |inner ℝ x n - inner ℝ y n| + |inner ℝ y n - β| := by
    simpa only [sub_add_sub_cancel] using abs_add_le
      (inner ℝ x n - inner ℝ y n) (inner ℝ y n - β)
  exact hs.trans ((add_le_add hi hy).trans_eq (by ring))

/-- A lower fine-state strip mass and an old joint cap force a strip floor
under the unchanged coarse reference. Fine-state mass cancels exactly. -/
theorem coarse_strip_floor_of_palette_joint_cap {Ω E : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S G : Set Ω) (hμS : μ Sᶜ = 0) (hGS : G ⊆ S)
    (f : Ω → E) (V : Ω → StripSpace) {a : ℝ} (ha : 0 < a)
    (hz : Measurable (fun x => velocityPalette a (V x)))
    (hfin : ((fun x => velocityPalette a (V x)) '' S).Finite)
    (T : ℝ) (hT : ∀ x ∈ S, ‖V x‖ ≤ T)
    (A θ : ℝ) (hA : 0 < A) (e : E) (he : 0 < μ.real {x | f x = e})
    (hcap : ∀ b, μ.real {x | x ∈ G ∧ f x = e ∧ velocityPalette a (V x) = b} ≤
      A * μ.real {x | f x = e} * μ.real {x | velocityPalette a (V x) = b})
    (n : StripSpace) (β r : ℝ) (hn : ‖n‖ = 1)
    (hstrip : θ * μ.real {x | f x = e} ≤
      μ.real {x | x ∈ G ∧ f x = e ∧ V x ∈ affineStrip n β r}) :
    θ / A ≤ μ.real {x | V x ∈ boundedStrip n β (r + 2 * a) T} := by
  classical
  let D := {x | x ∈ G ∧ f x = e ∧ V x ∈ affineStrip n β r}
  have hDsub : D ⊆ S := fun x hx => hGS hx.1
  have hDfin := hfin.subset (image_mono hDsub)
  let B := hDfin.toFinset
  have hsmall : μ.real D ≤ μ.real {x | x ∈ G ∧ f x = e ∧ velocityPalette a (V x) ∈ B} :=
    measureReal_mono (fun x hx => ⟨hx.1, hx.2.1, hDfin.mem_toFinset.mpr ⟨x, hx, rfl⟩⟩)
  have hsub : {x | velocityPalette a (V x) ∈ B} ∩ S ⊆
      {x | V x ∈ boundedStrip n β (r + 2 * a) T} := by
    intro x hx
    obtain ⟨y, hy, hbin⟩ := hDfin.mem_toFinset.mp hx.1
    refine ⟨?_, affineStrip_of_same_velocity_palette ha hn hbin.symm hy.2.2⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hT x hx.2
  have hPalette : μ.real {x | velocityPalette a (V x) ∈ B} ≤
      μ.real {x | V x ∈ boundedStrip n β (r + 2 * a) T} := by
    have heq : μ ({x | velocityPalette a (V x) ∈ B} ∩ S) =
        μ {x | velocityPalette a (V x) ∈ B} := measure_inter_conull hμS
    calc
      _ = μ.real ({x | velocityPalette a (V x) ∈ B} ∩ S) :=
        (congrArg ENNReal.toReal heq).symm
      _ ≤ _ := measureReal_mono hsub
  have hbound := (hstrip.trans hsmall).trans
    ((fine_palette_event_joint_cap μ G f (fun x => velocityPalette a (V x)) hz A e hcap B).trans
      (mul_le_mul_of_nonneg_left hPalette (mul_nonneg hA.le he.le)))
  have hcancel : θ ≤ A * μ.real {x | V x ∈ boundedStrip n β (r + 2 * a) T} := by
    apply (mul_le_mul_iff_right₀ he).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound
  exact (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using hcancel)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
