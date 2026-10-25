-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Filling.BroadLineFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Filling/BroadLineFamily.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Filling/BroadLineFamily.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit dcdf5bd50e74;
-- source Submission/Obl/k4_isotropic_path_improvement/BroadLineFamily.lean (session x0352).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.DeterminantBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling.BroadCells

/-!
Finite physical velocity-graph obstruction. A line family with broadly
distributed lifted directions in every occupied cell obeys the ambient
four-dimensional support budget. This joins x0358's determinant sampling
lemma to the determinant Kakeya and power-mean estimates.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling

open scoped BigOperators
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

/-- Weight of the lines whose radius-three tubes meet a physical cell. -/
def localLineWeight {n : ℕ} (a e : Fin n → EuclideanSpace ℝ (Fin 4)) (w : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin 4)) (k : Fin n) : ℝ :=
  w k * (lineTube 3 (a k) (e k)).indicator (fun _ => (1 : ℝ)) x

/-- A concrete finite-family form of the broad-cell obstruction. -/
theorem broad_line_family_support_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (n : ℕ) (a e : Fin n → EuclideanSpace ℝ (Fin 4)) (w : Fin n → ℝ),
      (∀ k, ‖e k‖ = 1) → (∀ k, 0 ≤ w k) →
      ∀ ρ c : ℝ, 0 ≤ ρ → 0 ≤ c →
      (∀ q : Fin m, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
        c * (∑ k, localLineWeight a e w (latticePoint (z q)) k) ≤
          ∑ k, if ρ ≤ Metric.infDist (e k) (V : Set (EuclideanSpace ℝ (Fin 4))) then
            localLineWeight a e w (latticePoint (z q)) k else 0) →
      (c * ρ) ^ 4 * (∑ q : Fin m, ∑ k, localLineWeight a e w (latticePoint (z q)) k) ^ 4 ≤
        (m : ℝ) * C ^ 3 * (∑ k, w k) ^ 4 := by
  classical
  obtain ⟨C, hC, hbudget⟩ := four_dimensional_broad_lattice_budget
  refine ⟨C, hC, ?_⟩
  intro m z hz n a e w he hw ρ c hρ hc hbroad
  let mass : Fin m → ℝ := fun q => ∑ k, localLineWeight a e w (latticePoint (z q)) k
  have hlocal (q : Fin m) (k : Fin n) : 0 ≤ localLineWeight a e w (latticePoint (z q)) k :=
    mul_nonneg (hw k) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hcell (q : Fin m) : (c * ρ) ^ 4 * mass q ^ 4 ≤
      tubeSum 3 (fun _ : Fin 4 => a) (fun _ : Fin 4 => e) (fun _ : Fin 4 => w)
        (latticePoint (z q)) := by
    have h := Breadth.det_weight_of_breadth e
      (localLineWeight a e w (latticePoint (z q))) (hlocal q) ρ c hρ hc (hbroad q)
    simpa only [tubeSum, mass, localLineWeight] using h
  have h := hbudget m z hz (fun _ => n) (fun _ => a) (fun _ => e) (fun _ => w)
    (fun _ k => he k) (fun _ k => hw k) mass ((c * ρ) ^ 4)
    (fun q => Finset.sum_nonneg (fun k _ => hlocal q k)) (by positivity) hcell
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Filling
