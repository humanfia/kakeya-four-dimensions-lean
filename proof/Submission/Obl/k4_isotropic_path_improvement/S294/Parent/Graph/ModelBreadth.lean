-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.ModelBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/ModelBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Per-fine-cell velocity breadth for `model_velocity_rows` from
per-cell planar velocity strip caps: lifted directions `(1, c4, c6)` near a
proper subspace of `ℝ³` lie in one planar strip
(`Switch.lift_near_subspace_subset_strip`).
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.ModelRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch.StripBreadth

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- The planar velocity `(c4, c6)` of a model line. -/
def modelPlanar (pm : Qualification.PhysicalModel) (l : Ln) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![pm.scalarCoefficients l 4, pm.scalarCoefficients l 6]

theorem liftDir_modelPlanar (pm : Qualification.PhysicalModel) (l : Ln) :
    Switch.liftDir (modelPlanar pm l) = WithLp.toLp 2 (pm.velocity l) := by
  unfold Switch.liftDir modelPlanar
  congr 1

/-- **Per-cell breadth from per-cell strip caps.** -/
theorem model_breadth_of_strip (pm : Qualification.PhysicalModel) (μ : Measure Ev)
    [IsFiniteMeasure μ] (current : Set Ev) (code : Ev → Fin 4 → ℤ)
    {U w r p : ℝ} (hU : 0 ≤ U) (hr0 : 0 ≤ r) (hrw : 2 * (U + 1) * r ≤ w) (hr : r ≤ 1 / 4)
    (hvel : ∀ z ∈ current, ‖modelPlanar pm z.1‖ ≤ U)
    (hstrip : ∀ label (n : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖n‖ = 1 →
      μ.real (current ∩ code ⁻¹' {label} ∩
          {z | |inner ℝ n (modelPlanar pm z.1) - t| ≤ w}) ≤
        p * μ.real (current ∩ code ⁻¹' {label}))
    (hmeas : ∀ label (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))),
      MeasurableSet (current ∩ code ⁻¹' {label} ∩
        {z | r ≤ Metric.infDist (WithLp.toLp 2 (pm.velocity z.1) : EuclideanSpace ℝ (Fin 3))
          (W : Set _)})) :
    ∀ label (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
      (1 - p) * μ.real (current ∩ code ⁻¹' {label}) ≤
        μ.real (current ∩ code ⁻¹' {label} ∩
          {z | r ≤ Metric.infDist (WithLp.toLp 2 (pm.velocity z.1) : EuclideanSpace ℝ (Fin 3))
            (W : Set _)}) := by
  intro label W hW
  obtain ⟨m, t, hm, hsub⟩ := Switch.lift_near_subspace_subset_strip W hW U w r hU hr0 hrw hr
  set A := current ∩ code ⁻¹' {label} with hA
  set G := {z : Ev | r ≤ Metric.infDist (WithLp.toLp 2 (pm.velocity z.1) :
    EuclideanSpace ℝ (Fin 3)) (W : Set _)} with hG
  have hnear : A \ (A ∩ G) ⊆ A ∩ {z | |inner ℝ m (modelPlanar pm z.1) - t| ≤ w} := by
    rintro z ⟨hzA, hzG⟩
    refine ⟨hzA, ?_⟩
    have hlt : Metric.infDist (Switch.liftDir (modelPlanar pm z.1)) (W : Set _) < r := by
      rw [liftDir_modelPlanar]
      by_contra hcon
      exact hzG ⟨hzA, not_lt.mp hcon⟩
    exact hsub _ (hvel z hzA.1) hlt
  have h1 : μ.real (A \ (A ∩ G)) ≤ p * μ.real A :=
    (measureReal_mono hnear).trans (hstrip label m t hm)
  have h2 : μ.real (A \ (A ∩ G)) = μ.real A - μ.real (A ∩ G) :=
    measureReal_sdiff inter_subset_left (hmeas label W)
  rw [h2] at h1
  linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
