-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.LikelihoodCut, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/LikelihoodCut.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/LikelihoodCut.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/LikelihoodCut.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/LikelihoodCut.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreparedLaw

/-! Turn the velocity window into a measurable omission under the unchanged
prepared law and a joint cap relative to its original coarse posterior. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Obl.k4_matching_cofinal_palette_selection

theorem measurable_historyLikelihood {Ω Ζ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ζ] [Countable Ζ] [MeasurableSingletonClass Ζ]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ) (k : ℕ)
    (hF : Measurable (F k)) (hZ : Measurable Z) :
    Measurable (supportLikelihood μ S F Z k) := by
  exact (measurable_of_countable (fun p : ℕ × Ζ =>
    (μ {y | y ∈ S ∧ F k y = p.1 ∧ Z y = p.2}).toReal /
      (μ {y | y ∈ S ∧ F k y = p.1}).toReal)).comp (hF.prodMk hZ)

def likelihoodGood {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (start stop : ℕ) (R : ℝ) : Set Ω :=
  {x | x ∈ S ∧ supportLikelihood μ S F Z stop x ≤ R * supportLikelihood μ S F Z start x}

theorem measurableSet_likelihoodGood {Ω Ζ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ζ] [Countable Ζ] [MeasurableSingletonClass Ζ]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (start stop : ℕ) (R : ℝ) (hS : MeasurableSet S)
    (hstart : Measurable (F start)) (hstop : Measurable (F stop)) (hZ : Measurable Z) :
    MeasurableSet (likelihoodGood μ S F Z start stop R) :=
  hS.inter (measurableSet_le (measurable_historyLikelihood μ S F Z stop hstop hZ)
    (measurable_const.mul (measurable_historyLikelihood μ S F Z start hstart hZ)))

theorem likelihoodGood_lost_mass {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (start C : ℕ) (R : ℝ) :
    μ (S \ likelihoodGood μ S F Z start (start + C) R) = badMass μ S F Z C start R := by
  apply congrArg μ
  ext x
  by_cases hx : x ∈ S <;> simp [likelihoodGood, hx, not_le]

theorem historyLikelihood_nonneg {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ) (k : ℕ) (x : Ω) :
    0 ≤ supportLikelihood μ S F Z k x :=
  div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem historyLikelihood_mul_record_mass {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω)
    (F : ℕ → Ω → ℕ) (Z : Ω → Ζ) (k : ℕ) (x : Ω) :
    supportLikelihood μ S F Z k x * μ.real {y | y ∈ S ∧ F k y = F k x} =
      μ.real {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x} := by
  have hle : μ.real {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x} ≤
      μ.real {y | y ∈ S ∧ F k y = F k x} :=
    measureReal_mono (fun y hy => ⟨hy.1, hy.2.1⟩)
  by_cases hz : μ.real {y | y ∈ S ∧ F k y = F k x} = 0
  · have hj : μ.real {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x} = 0 := by
      linarith [measureReal_nonneg (μ := μ) (s := {y | y ∈ S ∧ F k y = F k x ∧ Z y = Z x})]
    rw [hz, mul_zero, hj]
  · exact div_mul_cancel₀ _ hz

/-- After omitting the bad likelihood cells, every retained fine-history /
velocity cell is capped using the OLD fine-history mass and coarse posterior.
No surviving denominator appears on the right. -/
theorem likelihoodGood_joint_cap {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω)
    (F : ℕ → Ω → ℕ) (Z : Ω → Ζ) (start stop : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hnest : ∀ x ∈ S, ∀ y ∈ S, F stop x = F stop y → F start x = F start y)
    (x₀ : Ω) (hx₀ : x₀ ∈ S) :
    μ.real {x | x ∈ likelihoodGood μ S F Z start stop R ∧
      F stop x = F stop x₀ ∧ Z x = Z x₀} ≤
      R * μ.real {x | x ∈ S ∧ F stop x = F stop x₀} *
        supportLikelihood μ S F Z start x₀ := by
  let G := {x | x ∈ likelihoodGood μ S F Z start stop R ∧
    F stop x = F stop x₀ ∧ Z x = Z x₀}
  by_cases hne : G.Nonempty
  · obtain ⟨x, hx, hstop, hZ⟩ := hne
    have hstart := hnest x hx.1 x₀ hx₀ hstop
    have hgood : supportLikelihood μ S F Z stop x₀ ≤
        R * supportLikelihood μ S F Z start x₀ := by
      simpa only [supportLikelihood, hstart, hstop, hZ] using hx.2
    calc
      _ ≤ μ.real {x | x ∈ S ∧ F stop x = F stop x₀ ∧ Z x = Z x₀} :=
        measureReal_mono (fun x hx => ⟨hx.1.1, hx.2⟩)
      _ = supportLikelihood μ S F Z stop x₀ *
          μ.real {x | x ∈ S ∧ F stop x = F stop x₀} :=
        (historyLikelihood_mul_record_mass μ S F Z stop x₀).symm
      _ ≤ (R * supportLikelihood μ S F Z start x₀) *
          μ.real {x | x ∈ S ∧ F stop x = F stop x₀} :=
        mul_le_mul_of_nonneg_right hgood measureReal_nonneg
      _ = _ := by ring
  · have heq : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change μ.real G ≤ _
    rw [heq, measureReal_empty]
    exact mul_nonneg (mul_nonneg hR measureReal_nonneg)
      (historyLikelihood_nonneg μ S F Z start x₀)

/-- The likelihood cut selects whole original history/palette states. -/
theorem likelihoodGood_state_invariant {Ω Ζ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Set Ω) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ)
    (start stop : ℕ) (R : ℝ) {x y : Ω} (hx : x ∈ S) (hy : y ∈ S)
    (hstart : F start x = F start y) (hstop : F stop x = F stop y) (hZ : Z x = Z y) :
    x ∈ likelihoodGood μ S F Z start stop R ↔ y ∈ likelihoodGood μ S F Z start stop R := by
  simp only [likelihoodGood, mem_ofPred_eq, hx, hy, true_and,
    supportLikelihood, hstart, hstop, hZ]

/-- The window's exceptional mass bound gives an actual measurable sublaw,
with a joint cell ceiling against the frozen reference denominators. -/
theorem likelihood_window_cut {Ω Ζ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ζ] [Countable Ζ] [MeasurableSingletonClass Ζ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (F : ℕ → Ω → ℕ) (Z : Ω → Ζ) (start C : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hstart : Measurable (F start)) (hstop : Measurable (F (start + C))) (hZ : Measurable Z)
    (hnest : ∀ x ∈ S, ∀ y ∈ S, F (start + C) x = F (start + C) y → F start x = F start y)
    (α : ℝ) (hbad : badMass μ S F Z C start R ≤ ENNReal.ofReal α) :
    MeasurableSet (likelihoodGood μ S F Z start (start + C) R) ∧
    likelihoodGood μ S F Z start (start + C) R ⊆ S ∧
    μ (S \ likelihoodGood μ S F Z start (start + C) R) ≤ ENNReal.ofReal α ∧
    ∀ x₀ ∈ S, μ.real {x | x ∈ likelihoodGood μ S F Z start (start + C) R ∧
      F (start + C) x = F (start + C) x₀ ∧ Z x = Z x₀} ≤
      R * μ.real {x | x ∈ S ∧ F (start + C) x = F (start + C) x₀} *
        supportLikelihood μ S F Z start x₀ := by
  refine ⟨measurableSet_likelihoodGood μ S F Z start (start + C) R hS hstart hstop hZ,
    fun x hx => hx.1, ?_, ?_⟩
  · rw [likelihoodGood_lost_mass]
    exact hbad
  · exact likelihoodGood_joint_cap μ S F Z start (start + C) R hR hnest

/-- The measurable likelihood omission retains its original probability
mass. The surviving law is not renormalized. -/
theorem likelihood_window_retained_mass {Ω Ζ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ζ] [Countable Ζ] [MeasurableSingletonClass Ζ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (hμS : μ Sᶜ = 0) (F : ℕ → Ω → ℕ) (Z : Ω → Ζ) (start C : ℕ) (R : ℝ)
    (hstart : Measurable (F start)) (hstop : Measurable (F (start + C))) (hZ : Measurable Z)
    {α : ℝ} (hα : 0 ≤ α) (hbad : badMass μ S F Z C start R ≤ ENNReal.ofReal α) :
    ENNReal.ofReal (1 - α) ≤ μ (likelihoodGood μ S F Z start (start + C) R) := by
  let G := likelihoodGood μ S F Z start (start + C) R
  have hG : MeasurableSet G :=
    measurableSet_likelihoodGood μ S F Z start (start + C) R hS hstart hstop hZ
  have hsub : G ⊆ S := fun x hx => hx.1
  have hmassS : μ S = 1 := by
    simpa [hμS] using measure_add_measure_compl (μ := μ) hS
  have hdecomp : μ (S \ G) + μ G = 1 := by
    simpa only [Set.inter_eq_right.mpr hsub, hmassS] using measure_sdiff_add_inter (μ := μ) S hG
  have hlost : μ (S \ G) ≤ ENNReal.ofReal α := by
    rw [likelihoodGood_lost_mass]
    exact hbad
  rw [ENNReal.ofReal_sub 1 hα, ENNReal.ofReal_one]
  apply tsub_le_iff_left.mpr
  exact hdecomp.symm.trans_le (add_le_add hlost le_rfl)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
