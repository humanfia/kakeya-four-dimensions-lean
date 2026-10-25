-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMultiplicity, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMultiplicity.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMultiplicity.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMultiplicity.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMultiplicity.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAtlas

/-! Refined charts remain predictable from the original terminal observation.
The global midpoint-bin range never enters the multiplicity bound. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

namespace StripRefinement

variable {α : Type} [Fintype α] {W T : ℕ}
  (d : StripRefinement α) (p : α → StripParent W T)

open Classical in
theorem observation_multiplicity {N κ depth aL : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hr : 0 < d.radius)
    (oldList : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset α)
    (hknown : ∀ b x, x ∈ (p b).incidences →
      b ∈ oldList (p b).world (gobs (B (p b).world) aL x))
    (γ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    (Finset.univ.filter (fun a : d.Label => (p a.1).world = γ ∧
      ∃ x ∈ d.incidence p a, gobs (B γ) aL x = o)).card ≤
        (oldList γ o).card * (d.count * (2 * d.normalBudget + 1)) := by
  apply strip_midpoint_label_count d.normalBudget
    (fun a : d.Label => a.1) (fun a : d.Label => a.2.1)
    (fun a : d.Label => (a.2.2 : ℤ))
    (fun a a' h => Prod.ext (congrArg Sigma.fst h)
      (Prod.ext (congrArg (fun q : Σ _b : α, Σ _i : Fin d.count, ℤ => q.2.1) h)
        (Subtype.ext (congrArg (fun q : Σ _b : α, Σ _i : Fin d.count, ℤ => q.2.2) h))))
    (oldList γ o) (fun _ => d.radius) d.normal d.offset
    (fun b => (o.1 0 - (p b).start) / ((2 : ℝ) ^ T)⁻¹)
    (fun b => observedPacketPosition (p b).frame (p b).center (p b).velocity o)
    (fun a : d.Label => (p a.1).world = γ ∧
      ∃ x ∈ d.incidence p a, gobs (B γ) aL x = o)
  intro a ha
  obtain ⟨hw, x, hx, ho⟩ := ha
  have hxold := d.incidence_subset p a hx
  have hparent := hknown a.1 x hxold
  have ho' : gobs (B (p a.1).world) aL x = o := by simpa only [hw] using ho
  constructor
  · rwa [ho', hw] at hparent
  · rcases hold a.1 with ⟨_, _, _, _, _, _, _, _, _, _, hinc, _⟩
    have ht := (hinc x hxold).2.2.1
    have hend : (((p a.1).timeIndex : ℝ) + 1) / (2 : ℝ) ^ T =
        (p a.1).start + ((2 : ℝ) ^ T)⁻¹ := by unfold StripParent.start; ring
    have ht' : x.2 ∈ Set.Icc (p a.1).start ((p a.1).start + ((2 : ℝ) ^ T)⁻¹) := by
      constructor
      · exact ht.1
      · rw [← hend]
        exact ht.2
    have h := packet_midpoint_bin_known_of_obs_eq
      (p a.1).frame (p a.1).center (p a.1).velocity (d.normal a.1 a.2.1)
      (B (p a.1).world) aL (p a.1).start (((2 : ℝ) ^ T)⁻¹)
      d.radius (d.offset a.1 a.2.1) d.normalBudget x o
      (by positivity) hr ht' hx.2.1.2.1 ho'
    rw [hx.2.2] at h
    exact h

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
