-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.DenseJet.EighthBall, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/DenseJet/EighthBall.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/DenseJet/EighthBall.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/DenseJet/EighthBall.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/DenseJet/EighthBall.lean
-- Earlier source attributions below are retained.
import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison.SheetBounds
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet.RealJets

/-!
# The sheet Remez assertion on small balls

`SheetRemezAssertion` is, word for word, the frozen statement of o172
(`Submission.k4_algebraic_sheet_remez`). After the affine change `z ↦ y + z / 4` it
controls a degree-`D` sheet on the real ball of radius `1/8` around any point of the
closed unit ball from its values on a measurable subset of that ball.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet

open Set Metric MeasureTheory
open Submission.Obl.k4_algebraic_real_jet_comparison

/-- The frozen statement of o172 `Submission.k4_algebraic_sheet_remez`. -/
def SheetRemezAssertion : Prop := ∀ n D : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : MvPolynomial (Fin (n + 1)) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℂ), P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) → (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f z)) P = 0) → (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → (f (WithLp.toLp 2 (fun j => (x j : ℂ)))).im = 0) → ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ), MeasurableSet E → E ⊆ Metric.closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V → ENNReal.ofReal θ * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ MeasureTheory.volume E → (∀ x ∈ E, ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ V) → ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ C * θ ^ (-C) * V

lemma realSlice_affine (y x : EuclideanSpace ℝ (Fin 3)) :
    realSlice y + ((1 / 4 : ℝ) : ℂ) • (WithLp.toLp 2 (fun i => (x i : ℂ)) :
      EuclideanSpace ℂ (Fin 3)) = realSlice (y + (1 / 4 : ℝ) • x) := by
  ext i
  simp [realSlice_apply]

lemma mapsTo_quarter {y : EuclideanSpace ℝ (Fin 3)} (hy : ‖y‖ < 3) :
    MapsTo (fun z => realSlice y + ((1 / 4 : ℝ) : ℂ) • z) (ball 0 4) (ball 0 4) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz ⊢
  have hsm : ‖((1 / 4 : ℝ) : ℂ) • z‖ = ‖z‖ / 4 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    ring
  calc
    ‖realSlice y + ((1 / 4 : ℝ) : ℂ) • z‖ ≤ ‖realSlice y‖ + ‖((1 / 4 : ℝ) : ℂ) • z‖ :=
      norm_add_le _ _
    _ < 4 := by rw [hsm, norm_realSlice_apply]; linarith

/-- Rescaled preimage of a set near `y`: its volume is multiplied by `64`. -/
lemma volume_quarter_preimage (y : EuclideanSpace ℝ (Fin 3))
    (S : Set (EuclideanSpace ℝ (Fin 3))) :
    volume ((fun x : EuclideanSpace ℝ (Fin 3) => y + (1 / 4 : ℝ) • x) ⁻¹' S) = 64 * volume S := by
  have hcomp : ((fun x : EuclideanSpace ℝ (Fin 3) => y + (1 / 4 : ℝ) • x) ⁻¹' S) =
      (fun x : EuclideanSpace ℝ (Fin 3) => (1 / 4 : ℝ) • x) ⁻¹'
        ((fun z : EuclideanSpace ℝ (Fin 3) => y + z) ⁻¹' S) := rfl
  rw [hcomp, Measure.addHaar_preimage_smul volume (by norm_num : (1 / 4 : ℝ) ≠ 0),
    measure_preimage_add, finrank_euclideanSpace_fin]
  congr 1
  norm_num

/-- o172 on the real ball of radius `1/8` around a point of the closed unit ball. -/
theorem eighth_ball_remez (hR : SheetRemezAssertion) (D : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (F : EuclideanSpace ℂ (Fin 3) → ℂ), HasSheetRelation 3 D F →
      DifferentiableOn ℂ F (ball 0 4) →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ < 4 → (F (realSlice x)).im = 0) →
      ∀ (y : EuclideanSpace ℝ (Fin 3)), ‖y‖ ≤ 1 →
      ∀ (S : Set (EuclideanSpace ℝ (Fin 3))) (θ V : ℝ), MeasurableSet S →
        S ⊆ closedBall y (1 / 8) → 0 < θ → θ ≤ 1 → 0 ≤ V →
        ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤
          64 * volume S →
        (∀ x ∈ S, ‖F (realSlice x)‖ ≤ V) →
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x - y‖ ≤ 1 / 8 →
          ‖F (realSlice x)‖ ≤ C * θ ^ (-C) * V := by
  obtain ⟨C, hC, hrem⟩ := hR 3 D
  refine ⟨C, hC, ?_⟩
  intro F hrel hF hreal y hy S θ V hS hSsub hθ hθ1 hV hmass hbound x hx
  have hy3 : ‖y‖ < 3 := by linarith
  have hmap := mapsTo_quarter hy3
  obtain ⟨P, hP, hdeg, hroot⟩ :=
    hrel.comp_affine (realSlice y) (by norm_num : ((1 / 4 : ℝ) : ℂ) ≠ 0) hmap
  have hdG : DifferentiableOn ℂ (fun z => F (realSlice y + ((1 / 4 : ℝ) : ℂ) • z)) (ball 0 4) := by
    have hlin : Differentiable ℂ
        (fun z : EuclideanSpace ℂ (Fin 3) => realSlice y + ((1 / 4 : ℝ) : ℂ) • z) := by
      fun_prop
    exact hF.comp hlin.differentiableOn hmap
  let E' : Set (EuclideanSpace ℝ (Fin 3)) :=
    (fun x' : EuclideanSpace ℝ (Fin 3) => y + (1 / 4 : ℝ) • x') ⁻¹' S
  have hE' : MeasurableSet E' := by
    have hc : Continuous (fun x' : EuclideanSpace ℝ (Fin 3) => y + (1 / 4 : ℝ) • x') := by
      fun_prop
    exact hc.measurable hS
  have hE'sub : E' ⊆ closedBall 0 (1 / 2) := by
    intro x' hx'
    have h := hSsub hx'
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num)] at h
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hE'mass : ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤
      volume E' := by
    rw [volume_quarter_preimage y S]
    exact hmass
  have hrealG : ∀ x' : EuclideanSpace ℝ (Fin 3), ‖x'‖ ≤ 1 →
      ((fun z => F (realSlice y + ((1 / 4 : ℝ) : ℂ) • z))
        (WithLp.toLp 2 (fun j => (x' j : ℂ)))).im = 0 := by
    intro x' hx'
    simp only [realSlice_affine]
    apply hreal
    calc
      ‖y + (1 / 4 : ℝ) • x'‖ ≤ ‖y‖ + ‖(1 / 4 : ℝ) • x'‖ := norm_add_le _ _
      _ = ‖y‖ + ‖x'‖ / 4 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        ring
      _ < 4 := by linarith
  have hboundG : ∀ x' ∈ E', ‖(fun z => F (realSlice y + ((1 / 4 : ℝ) : ℂ) • z))
      (WithLp.toLp 2 (fun j => (x' j : ℂ)))‖ ≤ V := by
    intro x' hx'
    simp only [realSlice_affine]
    exact hbound _ hx'
  have hmain := hrem P _ hP hdeg hdG hroot hrealG E' θ V hE' hE'sub hθ hθ1 hV hE'mass hboundG
  have hx' : ‖(4 : ℝ) • (x - y)‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    linarith
  have h := hmain _ hx'
  simp only [realSlice_affine] at h
  have heq : y + (1 / 4 : ℝ) • ((4 : ℝ) • (x - y)) = x := by
    rw [smul_smul]
    norm_num
  rwa [heq] at h

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.DenseJet
