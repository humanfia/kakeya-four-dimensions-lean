-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.FourJetTimeRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/FourJetTimeRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 81bd965973abb9b4ad535c97f6727b79e93bbe0f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FourJetTimeRows.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomTimeRow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetWorldCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CanonicalParameterWorlds

/-! # Time-only rows with arbitrary original intercepts

Adapted from this LOT tree, o265, x0943 at 5207eac7,
Broad/Qualification/ZoomTimeRow.lean. Its original source is o106,
x0352 at 1e57792e. A common constant spatial translation removes the
three intercepts in each position comparison.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
noncomputable section

-- The two four-jet comparison declarations are already proved in ZoomTimeRow.lean.

/-- All rows are constructed before selecting any coefficient world.
The original trajectory labels, times and field remain unchanged. -/
theorem exists_canonical_world_time_rows_of_jets {Λ : Type*} (E : Set (Λ × ℝ))
    (c : Λ → Fin 7 → ℝ) (row : Λ × ℝ → Fin 2 → ℝ)
    (ρ K B L : ℝ) (hρ : 0 < ρ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (htime : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1| ≤ K ∧ |c z.1 2| ≤ K ∧ |c z.1 4| ≤ K ∧ |c z.1 6| ≤ K)
    (hbound : ∀ z∈E, ‖row z‖ ≤ B)
    (hfield : ∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      ‖row z-row z'‖ ≤ L*(‖zpos (c z.1) z.2-zpos (c z'.1) z'.2‖+ρ)) :
    ∃ F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ, (∀ q, Measurable (F q)) ∧
      (∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ B) ∧
      (∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2-row z‖ ≤ 2*((3*K+1)*L)*ρ) ∧
      (∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
        ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤
          3*((3*K+1)*L)*(|z.2-z'.2|+ρ)) := by
  classical
  let Ew (q : Fin 7 → ℤ) := {z∈E | parameterCode ρ (c z.1)=q}
  have hex (q : Fin 7 → ℤ) := exists_zoom_time_row_of_jets (Ew q) c row ρ K B L hρ hK hL
    (fun z hz => htime z hz.1) (fun z hz => hjets z hz.1)
    (by
      intro z hz z' hz' i
      have heq := congrFun (hz.2.trans hz'.2.symm) i
      exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hρ heq).le)
    (fun z hz => hbound z hz.1)
    (fun z hz z' hz' => hfield z hz.1 z' hz'.1 (hz.2.trans hz'.2.symm))
  choose F hFm hFb hFfit hFcmp using hex
  exact ⟨F,hFm,fun z hz => hFb _ z ⟨hz,rfl⟩,
    fun z hz => hFfit _ z ⟨hz,rfl⟩,fun z hz z' hz' hw =>
      by simpa only [hw] using hFcmp _ z ⟨hz,rfl⟩ z' ⟨hz',hw.symm⟩⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
