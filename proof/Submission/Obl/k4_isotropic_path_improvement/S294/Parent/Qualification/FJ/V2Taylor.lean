-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FJ.V2Taylor, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FJ/V2Taylor.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1030, commit c13f2967e10c3cba5027177f1097bb00019402ce,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FJ/V2Taylor.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FJ/V2Taylor.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 59f07e61. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2Hierarchy
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPrunedHierarchy

set_option autoImplicit false

/-!
# The first Taylor estimate in version 2 (paper `tex-05`, display `a04:first-taylor`)

On one common retained set (x0662's `exists_common_current_floor_set`, which depends only on the
retained times, the bound and the lengths), both components of the row satisfy the Taylor estimate
`|F(v) - F(u) - (v - u) A(u)| ≤ C H^(11/10)` with the vector row `A(t)` of the finest slopes
(x0662's `taylor_on_current_floor_set`, o078 branch `x0662` at `f2bac599`, applied to each
component hierarchy).
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable section

/-- The vector row of finest slopes of a version-2 hierarchy. -/
def V2Hierarchy.finestRow {Λ : Type*} [MeasurableSpace Λ] {n : ℕ} {ν : Measure Λ}
    {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ} {J : Fin (n + 1) → ℕ} {hJ : ∀ i, 0 < J i}
    {p : Fin (n + 1) → ℝ} {B : ℝ} (G : V2Hierarchy ν E F J hJ p B) (t : ℝ) : Fin 2 → ℝ :=
  fun k => (G.comp k).slope (Fin.last n) t

/-- **The first Taylor estimate for both components on one retained set.** -/
theorem V2Hierarchy.exists_taylor_restriction {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → Fin 2 → ℝ}
    {J : Fin (n + 1) → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin (n + 1) → ℝ} {B : ℝ}
    (G : V2Hierarchy ν E F J hJ p B) (hE : MeasurableSet E) (hB : 0 < B)
    (hmesh : Antitone (fun i => 1 / (J i : ℝ)))
    (hlower : ∀ j : Fin n,
      (1 / (J j.castSucc : ℝ)) ^ (33 / 32 : ℝ) / 2 ≤ 1 / (J j.succ : ℝ))
    (hreading : ∀ i, p i ≤ 2 * (1 / (J i : ℝ)) ^ (1 / 4 : ℝ))
    (hnesting : ∀ i j, i ≤ j → ∀ t ∈ (G.comp 0).times, ∀ u ∈ (G.comp 0).times,
      scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u →
      scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u) :
    ∃ R : Set (Λ × ℝ), MeasurableSet R ∧ R ⊆ E ∩ (univ ×ˢ (G.comp 0).times) ∧
      (2 * B)⁻¹ ≤ (ν.prod volume).real R ∧
      (∀ q ∈ R, ∀ i,
        ENNReal.ofReal ((1 / (J i : ℝ)) / (4 * (n + 1 : ℕ) * B)) ≤
          (ν.prod volume) (R ∩
            (univ ×ˢ timeCell (J i) (scalarTimeBlockCode (J i) (hJ i) q.2)))) ∧
      ∀ q ∈ R, ∀ q' ∈ R, ∀ i,
        scalarTimeBlockCode (J i) (hJ i) q.2 = scalarTimeBlockCode (J i) (hJ i) q'.2 →
        ∀ k, |F q'.2 k - F q.2 k - (q'.2 - q.2) * G.finestRow q.2 k| ≤
          (4 * B + 32 * (n : ℝ) * B * (4 * (n + 1 : ℕ) * B)) *
            (1 / (J i : ℝ)) ^ (11 / 10 : ℝ) := by
  obtain ⟨R, hRm, hRP, hmass, hfloor⟩ := (G.comp 0).exists_common_current_floor_set hE hB
  refine ⟨R, hRm, hRP, hmass, hfloor, ?_⟩
  intro q hq q' hq' i hcode k
  have htimes : ∀ k, (G.comp k).times = (G.comp 0).times := by
    intro k
    fin_cases k
    · rfl
    · exact G.times_eq
  have hRk : R ⊆ E ∩ (univ ×ˢ (G.comp k).times) := by
    rw [htimes k]; exact hRP
  have hnestk : ∀ i j, i ≤ j → ∀ t ∈ (G.comp k).times, ∀ u ∈ (G.comp k).times,
      scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u →
      scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u := by
    rw [htimes k]; exact hnesting
  exact (G.comp k).taylor_on_current_floor_set hB.le (by positivity) hmesh hlower hreading
    hnestk hRk hfloor q hq q' hq' i hcode

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FJ.V2
