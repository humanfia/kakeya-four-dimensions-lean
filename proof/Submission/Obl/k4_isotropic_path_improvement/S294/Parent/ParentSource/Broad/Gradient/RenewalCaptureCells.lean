-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.RenewalCaptureCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/RenewalCaptureCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit af69463910936c02b3e287e9153c4781be3e7639,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/RenewalCaptureCells.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.GradientCaptureAlternative
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RenewalCells

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric

noncomputable section

/-- One additional power in the explicit renewal radius absorbs the
extra low-cell norming error in the strip-capture alternative. -/
theorem renewal_capture_radius_absorbs
    {K A B δ : ℝ} {J q : ℕ} (hK : 2 ≤ K) (hA : 2 ≤ A) (hAK : A ≤ K)
    (hB : 0 ≤ B) (hBK : B ≤ K) (hδ : 0 < δ) (hδfloor : (K^q)⁻¹ ≤ δ) :
    (3*A^J)*((1+(B+2)/δ)*(1+2*B)+1)*
      (3*(8:ℝ)^J*renewalCellRadius K J (q+1)) ≤ 1/2 := by
  have hKp : 0 < K := by linarith
  have hAp : 0 < A := by linarith
  let C := (1+(B+2)/δ)*(1+2*B)
  have hC : 1 ≤ C := by
    have h1 : 1 ≤ 1+(B+2)/δ := by
      have hh : 0 ≤ (B+2)/δ := by positivity
      linarith
    have h2 : 1 ≤ 1+2*B := by linarith
    calc
      1 = (1:ℝ)*1 := by ring
      _ ≤ (1+(B+2)/δ)*(1+2*B) := mul_le_mul h1 h2 (by norm_num) (by linarith)
  have hr : renewalCellRadius K J (q+1)*K=renewalCellRadius K J q := by
    unfold renewalCellRadius
    rw [show 4*J+(q+1)+12=(4*J+q+12)+1 by omega,pow_succ]
    field_simp
  have hnonneg : 0 ≤ (3*A^J)*(C+1)*(3*(8:ℝ)^J*renewalCellRadius K J (q+1)) := by
    unfold renewalCellRadius
    positivity
  have hsmall := (renewalCellRadius_absorbs (J := J) hK hA hAK hB hBK hδ hδfloor).2
  have hmul : ((3*A^J)*(C+1)*(3*(8:ℝ)^J*renewalCellRadius K J (q+1)))*K ≤ 1 := by
    calc
      _ = (3*A^J)*(3*(8:ℝ)^J*renewalCellRadius K J q)*(C+1) := by
        calc
          _ = (3*A^J)*(3*(8:ℝ)^J*(renewalCellRadius K J (q+1)*K))*(C+1) := by ring
          _ = _ := by rw [hr]
      _ ≤ (3*A^J)*(3*(8:ℝ)^J*renewalCellRadius K J q)*(2*C) := by
        apply mul_le_mul_of_nonneg_left (by linarith : C+1 ≤ 2*C)
        unfold renewalCellRadius
        positivity
      _ = 2*((3*A^J)*(1+(B+2)/δ)*
          (3*(8:ℝ)^J*renewalCellRadius K J q*(1+2*B))) := by dsimp [C]; ring
      _ ≤ 1 := by linarith
  have htwice := mul_le_mul_of_nonneg_left hK hnonneg
  change (3*A^J)*(C+1)*(3*(8:ℝ)^J*renewalCellRadius K J (q+1)) ≤ 1/2
  nlinarith

/-- The concrete floor code itself supplies measurable bounded regions
and anchors, including empty cells, without a source geometry oracle. -/
theorem exists_renewal_capture_regions {K : ℝ} (hK : 2 ≤ K) (J q : ℕ) :
    ∃ (region : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
      (anchor : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 3)),
      (∀ i, MeasurableSet (region i)) ∧
      (∀ i, region i⊆closedBall 0 1) ∧
      (∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        x∈region (renewalCellCode K J q x)) ∧
      (∀ i, anchor i∈closedBall 0 1) ∧
      ∀ i x, x∈region i → ‖x-anchor i‖ ≤ renewalCellRadius K J q := by
  classical
  let region := fun i : Fin 3 → ℤ =>
    closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1∩(renewalCellCode K J q) ⁻¹' {i}
  have hanchors (i : Fin 3 → ℤ) : ∃ a∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ x∈region i, ‖x-a‖ ≤ renewalCellRadius K J q := by
    by_cases hi : (region i).Nonempty
    · obtain ⟨a,ha⟩ := hi
      refine ⟨a,ha.1,fun x hx => renewalCellCode_diameter hK J q ?_⟩
      exact hx.2.trans ha.2.symm
    · exact ⟨0,by simp,fun x hx => (hi ⟨x,hx⟩).elim⟩
  choose anchor hanchor hnear using hanchors
  refine ⟨region,anchor,?_,(fun i => inter_subset_left),?_,hanchor,hnear⟩
  · intro i
    exact measurableSet_closedBall.inter
      ((measurable_renewalCellCode K J q) (measurableSet_singleton i))
  · exact fun x hx => ⟨hx,rfl⟩

/-- Actual original-law tests on the explicit renewal code give either
whole-core gradient control or a table of strip predictions covering all
but one original floor. Only a fixed POWER mesh is chosen here. -/
theorem original_renewal_gradient_or_strip_capture
    {D J : ℕ} (hjets : ValueJetBound D J)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin 3)) (hZ : Measurable Z)
    (V : Ω → EuclideanSpace ℝ (Fin 2)) (hV : Measurable V)
    (S : Set Ω) (hS : MeasurableSet S)
    (hcore : ∀ ω∈S, Z ω∈closedBall 0 1)
    (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ContDiffOn ℝ 2 g (ball 0 4))
    (hgext : ∀ j : Fin 3, exf D (gradientComponent g j))
    {K A β δ E B : ℝ} {q : ℕ} (hK : 2 ≤ K) (hA : 2 ≤ A) (hAK : A ≤ K)
    (hβ : 0 < β) (hδ : 0 < δ) (hδfloor : (K^q)⁻¹ ≤ δ)
    (hE : 0 ≤ E) (hB : 0 ≤ B) (hBK : B ≤ K)
    (hcap : ∀ U, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β*volume U)
    (hspeed : ∀ ω∈S, ‖V ω‖ ≤ B)
    (htest : ∀ ω∈S, |fderiv ℝ g (Z ω) (spacetimeDirection (V ω))| ≤ E) :
    (∀ x∈closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
      ‖fderiv ℝ g x‖ ≤ 6*A^J*(1+(B+2)/δ)*E) ∨
    ∃ (normal : (Fin 3 → ℤ) → EuclideanSpace ℝ (Fin 2)) (center : (Fin 3 → ℤ) → ℝ),
      (∀ i, ‖normal i‖=1 ∧ |center i| ≤ B+δ) ∧
      MeasurableSet (⋃ i, (renewalCellCode K J (q+1) ∘ Z) ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) ∧
      μ (S\⋃ i, (renewalCellCode K J (q+1) ∘ Z) ⁻¹' {i}∩
        V ⁻¹' Submission.Lib.K4VelocityStrips.affineStrip (normal i) (center i) δ) <
          ENNReal.ofReal (β/A) := by
  obtain ⟨region,anchor,hm,hball,hcover,hanchor,hnear⟩ := exists_renewal_capture_regions hK J (q+1)
  have hcode : Measurable (renewalCellCode K J (q+1) ∘ Z) :=
    (measurable_renewalCellCode K J (q+1)).comp hZ
  exact original_entry_gradient_or_strip_capture hjets μ Z V hV S hS
    (renewalCellCode K J (q+1) ∘ Z) (fun i => hcode (measurableSet_singleton i))
    region hm hball (fun ω hω => hcover (Z ω) (hcore ω hω)) anchor hanchor
    g hg hgext hA hβ hδ hE (by unfold renewalCellRadius; positivity) hB hcap hnear
    hspeed htest (renewal_capture_radius_absorbs hK hA hAK hB hBK hδ hδfloor)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
