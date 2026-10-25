-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripCoverage, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripCoverage.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripCoverage.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripCoverage.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripCoverage.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

/-! A covered original residual supplies the full mass floor required by the
strip system, independently of the probability law used for packing strips. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped BigOperators

namespace StripRefinement

variable {α : Type} [Fintype α] {W T : ℕ}
  (d : StripRefinement α) (p : α → StripParent W T)

theorem weighted_covered_mass_le
    (μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ω : Fin W → ℝ)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ w, H w ⊆ {x | ∃ b, (p b).world = w ∧ x ∈ d.coveredIncidences p b}) :
    (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≤
      ∑ b, ENNReal.ofReal (ω (p b).world) * μ (p b).world (d.coveredIncidences p b) := by
  classical
  have h := weighted_residual_mass_le_sum μ ω (fun _b : α => 0) (fun b => (p b).world)
    (d.coveredIncidences p) H 0 (fun w x hx => by
      obtain ⟨b, hw, hb⟩ := hcover w hx
      exact ⟨b, rfl, hw, hb⟩)
  calc
    _ ≤ ∑ b, ENNReal.ofReal (ω (p b).world) *
        μ (p b).world (H (p b).world ∩ d.coveredIncidences p b) := by simpa only [ite_true] using h
    _ ≤ _ := Finset.sum_le_sum (fun b _ =>
      mul_le_mul_of_nonneg_left (measure_mono inter_subset_right) zero_le)

/-- The packed net covers the same original residual as the raw state strips.
The raw and packed strip palettes play no role in this original-law bound. -/
theorem weighted_mass_of_raw_strip_cover {ι : α → Type}
    (n : (b : α) → ι b → StripSpace) (β : (b : α) → ι b → ℝ)
    {r Tvel : ℝ}
    (hnet : ∀ b i V, ‖V‖ ≤ Tvel → V ∈ affineStrip (n b i) (β b i) r →
      V ∈ ⋃ j, affineStrip (d.normal b j) (d.offset b j) ((d.normalBudget : ℝ) * d.radius))
    (hbound : ∀ b x, x ∈ (p b).incidences →
      ‖packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity x.1‖ ≤ Tvel)
    (μ : Fin W → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (ω : Fin W → ℝ)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ w, H w ⊆ {x | ∃ b, (p b).world = w ∧ x ∈ (p b).incidences ∧
      ∃ i, packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity x.1 ∈
        affineStrip (n b i) (β b i) r}) :
    (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≤
      ∑ b, ENNReal.ofReal (ω (p b).world) * μ (p b).world (d.coveredIncidences p b) := by
  apply d.weighted_covered_mass_le p μ ω H
  intro w x hx
  obtain ⟨b, hw, hxb, i, hxi⟩ := hcover w hx
  exact ⟨b, hw, hxb, hnet b i _ (hbound b x hxb) hxi⟩

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
