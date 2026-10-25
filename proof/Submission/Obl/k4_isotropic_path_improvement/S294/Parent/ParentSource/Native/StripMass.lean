-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMass.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMass.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMass.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAtlas

/-! Exact mass accounting for the old-level strip refinement, always under the
original measures on incidences. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

namespace StripRefinement

variable {α : Type} {W T : ℕ} (d : StripRefinement α) (p : α → StripParent W T)

def coveredIncidences (b : α) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  (p b).incidences ∩
    (fun x => packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity x.1) ⁻¹'
      (⋃ i, affineStrip (d.normal b i) (d.offset b i) ((d.normalBudget : ℝ) * d.radius))

/-- Every covered old incidence goes to exactly one refined trajectory piece. -/
theorem iUnion_incidence {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hr : 0 < d.radius)
    (hn : ∀ b i, ‖d.normal b i‖ = 1) (hbins : κ ≤ (d.bins : ℝ) * d.radius)
    (b : α) :
    (⋃ q : Fin d.count × {z : ℤ // z ∈ stripBinRange d.bins},
      d.incidence p (b, q)) = d.coveredIncidences p b := by
  rcases hold b with ⟨_, _, _, _, _, _, _, _, _, hgeo, hinc, _⟩
  have hq : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hmid : (p b).start + ((2 : ℝ) ^ T)⁻¹ / 2 ∈
      Set.Icc (((p b).timeIndex : ℝ) / (2 : ℝ) ^ T)
        ((((p b).timeIndex : ℝ) + 1) / (2 : ℝ) ^ T) := by
    change _ ∈ Set.Icc (p b).start _
    have hend : (((p b).timeIndex : ℝ) + 1) / (2 : ℝ) ^ T =
        (p b).start + ((2 : ℝ) ^ T)⁻¹ := by unfold StripParent.start; ring
    rw [hend]
    constructor <;> linarith
  have hpart := iUnion_stripAssignment (p b).trajectories
    (packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity)
    (fun l => packetPosition (p b).frame (p b).center (p b).velocity l
      ((p b).start + ((2 : ℝ) ^ T)⁻¹ / 2))
    (d.normal b) (d.offset b) (w := (d.normalBudget : ℝ) * d.radius) hr (hn b)
    (fun l hl => ((hgeo l hl).2.2 _ hmid).1.trans hbins)
  ext x
  constructor
  · intro hx
    obtain ⟨q, hx⟩ := Set.mem_iUnion.mp hx
    exact ⟨hx.1, Set.mem_iUnion.mpr ⟨q.1, hx.2.1.2.1⟩⟩
  · intro hx
    have hA : x.1 ∈ (p b).trajectories := (hinc x hx.1).2.1
    have hpart' : x.1 ∈ (⋃ q : Fin d.count × {z : ℤ // z ∈ stripBinRange d.bins},
        stripAssignment (p b).trajectories
          (packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity)
          (fun l => packetPosition (p b).frame (p b).center (p b).velocity l
            ((p b).start + ((2 : ℝ) ^ T)⁻¹ / 2))
          (d.normal b) (d.offset b) ((d.normalBudget : ℝ) * d.radius) d.radius q.1 q.2) := by
      rw [hpart]
      exact ⟨hA, hx.2⟩
    obtain ⟨q, hpart'⟩ := Set.mem_iUnion.mp hpart'
    exact Set.mem_iUnion.mpr ⟨q, hx.1, hpart'⟩

theorem sum_incidence_measure {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hr : 0 < d.radius)
    (hn : ∀ b i, ‖d.normal b i‖ = 1) (hbins : κ ≤ (d.bins : ℝ) * d.radius)
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (b : α) :
    (∑ q : Fin d.count × {z : ℤ // z ∈ stripBinRange d.bins},
      μ (d.incidence p (b, q))) = μ (d.coveredIncidences p b) := by
  classical
  rw [← d.iUnion_incidence p hold hr hn hbins b, measure_iUnion]
  · exact (tsum_fintype _).symm
  · intro q q' hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hneq : (q.1, (q.2 : ℤ)) ≠ (q'.1, (q'.2 : ℤ)) := by
      intro h
      apply hne
      exact Prod.ext (congrArg (fun q : Fin d.count × ℤ => q.1) h)
        (Subtype.ext (congrArg (fun q : Fin d.count × ℤ => q.2) h))
    exact Set.disjoint_left.mp (stripAssignment_disjoint _ _ _ _ _ _ _ hneq) hx.2 hy.2
  · intro q
    apply d.measurableSet_incidence p _ _ (b, q)
    · intro b
      rcases hold b with ⟨_, _, _, _, _, _, h, _⟩
      exact h
    · intro b
      rcases hold b with ⟨_, _, _, _, _, _, _, h, _⟩
      exact h

/-- The original world weights factor through the refinement. No conditional
or normalized law occurs in this identity. -/
theorem sum_weighted_incidence [Fintype α] {N κ depth : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hr : 0 < d.radius)
    (hn : ∀ b i, ‖d.normal b i‖ = 1) (hbins : κ ≤ (d.bins : ℝ) * d.radius)
    (ω : Fin W → ℝ) (μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
    (∑ a : d.Label, ENNReal.ofReal (ω (p a.1).world) *
      μ (p a.1).world (d.incidence p a)) =
    ∑ b : α, ENNReal.ofReal (ω (p b).world) *
      μ (p b).world (d.coveredIncidences p b) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  change (∑ q : Fin d.count × {z : ℤ // z ∈ stripBinRange d.bins},
    ENNReal.ofReal (ω (p b).world) * μ (p b).world (d.incidence p (b, q))) = _
  rw [← Finset.mul_sum, d.sum_incidence_measure p hold hr hn hbins]

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
