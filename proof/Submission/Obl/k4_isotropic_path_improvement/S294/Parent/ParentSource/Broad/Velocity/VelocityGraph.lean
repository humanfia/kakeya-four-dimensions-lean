-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.VelocityGraph, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/VelocityGraph.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/VelocityGraph.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit d78c43c7c261;
-- source Submission/Obl/k4_isotropic_path_improvement/VelocityGraph.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CellBreadth

/-! A measurable physical velocity row outside the broad fine states. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set Module
open SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

set_option backward.isDefEq.respectTransparency false in
/-- Base breadth and failure of four-dimensional breadth give a measurable
physical row. The broad-cell mass is isolated for the native MK4 estimate. -/
theorem rows_outside_broad_cells_on {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Fin m) (hcode : Measurable code)
    (H : Set Ω) (hH : MeasurableSet H) (hHfull : μ Hᶜ = 0)
    (e : Ω → EuclideanSpace ℝ (Fin 3)) (w : Ω → ℝ)
    (hdir : Measurable fun x => unitTangent (liftedVector (e x) (w x)))
    (ρ ε c cbase K : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hcbase : c < cbase) (hK : 1 ≤ K)
    (he : ∀ x ∈ H, ∀ j, |e x j| ≤ K) (hw : ∀ x ∈ H, |w x| ≤ K)
    (hnorm : ∀ x ∈ H, ‖liftedVector (e x) (w x)‖ ≤ K)
    (hbroad : ∀ i, cellBroad μ code e ρ cbase i)
    (hcondition : 1 ≤ K * ρ ^ 3) (hsmall : 36 * K ^ 3 * (K * ε) ≤ 1) :
    ∃ (G : Fin m → Fin 3 → ℝ) (T : Set Ω),
      MeasurableSet T ∧ Measurable (fun x => G (code x)) ∧
      (∀ i j, |G i j| ≤ 28 * K ^ 6) ∧
      μ.real Tᶜ ≤ μ.real {x | cellBroad μ code
        (fun y => unitTangent (liftedVector (e y) (w y))) ε c (code x)} + c * μ.real univ ∧
      ∀ x ∈ T, x ∈ H ∧ |w x - ∑ j, G (code x) j * e x j| ≤ 80 * K ^ 7 * ε := by
  classical
  let laws (i : Fin m) := μ.restrict (code ⁻¹' {i})
  let d (x : Ω) := unitTangent (liftedVector (e x) (w x))
  let Broad (i : Fin m) := cellBroad μ code d ε c i
  have hplanes (i : Fin m) : ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)),
      finrank ℝ V < 4 ∧ (¬ Broad i →
        (laws i).real {x | ε ≤ Metric.infDist (d x) (V : Set _)} < c * (laws i).real univ) := by
    by_cases hi : Broad i
    · exact ⟨⊥, by simp, fun h => False.elim (h hi)⟩
    · change ¬ ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), finrank ℝ V < 4 →
        c * (laws i).real univ ≤
          (laws i).real {x | ε ≤ Metric.infDist (d x) (V : Set _)} at hi
      push Not at hi
      obtain ⟨V, hV, hmass⟩ := hi
      exact ⟨V, hV, fun _ => hmass⟩
  choose V hV houtside using hplanes
  let Q (i : Fin m) := H ∩ {x | ε ≤ Metric.infDist (d x) (V i : Set _)}ᶜ
  have hd : Measurable d := hdir
  have hQ (i : Fin m) : MeasurableSet (Q i) := by
    apply hH.inter
    apply MeasurableSet.compl
    exact measurableSet_le measurable_const ((Metric.continuous_infDist_pt _).measurable.comp hd)
  have hHcell (i : Fin m) : (laws i) Hᶜ = 0 :=
    le_antisymm (((Measure.restrict_le_self (μ := μ) (s := code ⁻¹' {i})) Hᶜ).trans hHfull.le) zero_le
  have hcost (i : Fin m) (hi : ¬ Broad i) : (laws i).real (Q i)ᶜ < c * (laws i).real univ := by
    have heq : (Q i)ᶜ = Hᶜ ∪ {x | ε ≤ Metric.infDist (d x) (V i : Set _)} := by
      simp only [Q, compl_inter, compl_compl]
    rw [heq]
    have h := measureReal_union_le (μ := laws i) Hᶜ
      {x | ε ≤ Metric.infDist (d x) (V i : Set _)}
    simp only [measureReal_def, hHcell i, ENNReal.toReal_zero, zero_add] at h
    exact h.trans_lt (houtside i hi)
  have hrows (i : Fin m) : ∃ G : Fin 3 → ℝ,
      (∀ j, |G j| ≤ 28 * K ^ 6) ∧ (¬ Broad i → ∀ x ∈ Q i,
        |w x - ∑ j, G j * e x j| ≤ 80 * K ^ 6 * (K * ε)) := by
    by_cases hi : Broad i
    · exact ⟨fun _ => 0, (fun _ => by simp; positivity), fun h => False.elim (h hi)⟩
    · have hloss : (laws i).real (Q i)ᶜ < cbase * (laws i).real univ :=
        (hcost i hi).trans_le (mul_le_mul_of_nonneg_right hcbase.le measureReal_nonneg)
      obtain ⟨G, hG, hfit⟩ := exists_row_on_captured_broad_law (laws i) e w
        ρ cbase K (K * ε) hρ hK (by positivity) (Q i) hloss (hbroad i)
        (fun x hx j => he x hx.1 j) (fun x hx => hw x hx.1) hcondition (V i) (hV i)
        (fun x hx => by
          have hx' : ¬ ε ≤ Metric.infDist (unitTangent (liftedVector (e x) (w x))) (V i : Set _) := hx.2
          exact raw_plane_distance_bound (V i) (liftedVector (e x) (w x)) K ε
            (hnorm x hx.1) (lt_of_not_ge hx').le) hsmall
      exact ⟨G, hG, fun _ => hfit⟩
  choose G hG hfit using hrows
  obtain ⟨T, hT, hloss, hmem⟩ := select_reference_states μ code hcode Broad Q hQ c hc
    (fun i hi => (hcost i hi).le)
  refine ⟨G, T, hT, (measurable_of_finite G).comp hcode, hG, hloss, ?_⟩
  intro x hx
  obtain ⟨hn, hxQ⟩ := hmem x hx
  exact ⟨hxQ.1, (hfit (code x) hn x hxQ).trans_eq (by ring)⟩

/-- Whole-space version of the physical row selection. -/
theorem rows_outside_broad_cells {m : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Fin m) (hcode : Measurable code)
    (e : Ω → EuclideanSpace ℝ (Fin 3)) (w : Ω → ℝ)
    (hdir : Measurable fun x => unitTangent (liftedVector (e x) (w x)))
    (ρ ε c cbase K : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hcbase : c < cbase) (hK : 1 ≤ K)
    (he : ∀ x j, |e x j| ≤ K) (hw : ∀ x, |w x| ≤ K)
    (hnorm : ∀ x, ‖liftedVector (e x) (w x)‖ ≤ K)
    (hbroad : ∀ i, cellBroad μ code e ρ cbase i)
    (hcondition : 1 ≤ K * ρ ^ 3) (hsmall : 36 * K ^ 3 * (K * ε) ≤ 1) :
    ∃ (G : Fin m → Fin 3 → ℝ) (T : Set Ω),
      MeasurableSet T ∧ Measurable (fun x => G (code x)) ∧
      (∀ i j, |G i j| ≤ 28 * K ^ 6) ∧
      μ.real Tᶜ ≤ μ.real {x | cellBroad μ code
        (fun y => unitTangent (liftedVector (e y) (w y))) ε c (code x)} + c * μ.real univ ∧
      ∀ x ∈ T, |w x - ∑ j, G (code x) j * e x j| ≤ 80 * K ^ 7 * ε := by
  obtain ⟨G, T, hT, hGmeas, hG, hloss, hfit⟩ := rows_outside_broad_cells_on μ code hcode
    univ MeasurableSet.univ (by simp) e w hdir ρ ε c cbase K hρ hε hc hcbase hK
    (fun x _ j => he x j) (fun x _ => hw x) (fun x _ => hnorm x) hbroad hcondition hsmall
  exact ⟨G, T, hT, hGmeas, hG, hloss, fun x hx => (hfit x hx).2⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
