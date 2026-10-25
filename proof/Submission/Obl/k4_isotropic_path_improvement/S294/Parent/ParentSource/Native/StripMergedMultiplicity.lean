-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedMultiplicity, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedMultiplicity.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedMultiplicity.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedMultiplicity.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedMultiplicity.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedAtlas

/-! The final list counts coarse parameter bins predicted by the original
fine packet. The size of the heavy net does not enter this bound. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

namespace StripRefinement

variable {α : Type} [Fintype α] {W T : ℕ}
  (d : StripRefinement α) (p : α → StripParent W T)

abbrev MergedParameterLabel := Σ b : α, StripCodeLabel d.radius (d.normal b) (d.offset b)

def mergedParameterLabel (a : d.MergedLabel) : d.MergedParameterLabel := ⟨a.1, a.2.1⟩

theorem merged_label_code_injective : Function.Injective
    (fun a : d.MergedLabel =>
      (⟨d.mergedParameterLabel a, ⟨(0 : Fin 1), (a.2.2 : ℤ)⟩⟩ :
        Σ _v : d.MergedParameterLabel, Σ _i : Fin 1, ℤ)) := by
  intro a a' h
  rcases a with ⟨b, q, z⟩
  rcases a' with ⟨b', q', z'⟩
  have hb : b = b' := congrArg (fun v => v.1.1) h
  subst b'
  have hq : q = q' := by
    apply (sigma_mk_injective
      (β := fun b : α => StripCodeLabel d.radius (d.normal b) (d.offset b)) (i := b))
    exact congrArg Sigma.fst h
  have hz : (z : ℤ) = (z' : ℤ) := congrArg (fun v => v.2.2) h
  exact congrArg (fun v => (Sigma.mk b v : d.MergedLabel))
    (Prod.ext hq (Subtype.ext hz))

open Classical in
/-- Once the coarse parameter label is terminal-known, only the short
midpoint list remains. In particular, there is no heavy-net-size factor. -/
theorem merged_observation_multiplicity {N κ depth aL w : ℝ} {M D : ℕ}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hr : 0 < d.radius) (hκ : 1 ≤ κ)
    (hV : ∀ b l, l ∈ (p b).trajectories →
      ‖packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity l‖ ≤ 2 * κ)
    (hwidth : w + 3 * (1 + 2 * κ) * d.radius ≤ (d.normalBudget : ℝ) * d.radius)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (paramList : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset d.MergedParameterLabel)
    (hknown : ∀ a x, x ∈ d.mergedIncidence p w success a →
      d.mergedParameterLabel a ∈ paramList (p a.1).world (gobs (B (p a.1).world) aL x))
    (γ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    (Finset.univ.filter (fun a : d.MergedLabel => (p a.1).world = γ ∧
      ∃ x ∈ d.mergedIncidence p w success a, gobs (B γ) aL x = o)).card ≤
        (paramList γ o).card * (2 * d.normalBudget + 1) := by
  let n : d.MergedParameterLabel → Fin 1 → StripSpace := fun v _ =>
    d.normal v.1 (canonicalStripIndex d.radius (d.normal v.1) (d.offset v.1) v.2)
  let β : d.MergedParameterLabel → Fin 1 → ℝ := fun v _ =>
    d.offset v.1 (canonicalStripIndex d.radius (d.normal v.1) (d.offset v.1) v.2)
  have h := strip_midpoint_label_count d.normalBudget d.mergedParameterLabel
    (fun _a : d.MergedLabel => (0 : Fin 1)) (fun a : d.MergedLabel => (a.2.2 : ℤ))
    d.merged_label_code_injective (paramList γ o) (fun _ => d.radius) n β
    (fun v => (o.1 0 - (p v.1).start) / ((2 : ℝ) ^ T)⁻¹)
    (fun v => observedPacketPosition (p v.1).frame (p v.1).center (p v.1).velocity o)
    (fun a : d.MergedLabel => (p a.1).world = γ ∧
      ∃ x ∈ d.mergedIncidence p w success a, gobs (B γ) aL x = o) (fun a ha => ?_)
  · simpa only [one_mul] using h
  obtain ⟨hw, x, hx, ho⟩ := ha
  have hxold := d.mergedIncidence_subset p w success a hx
  have ho' : gobs (B (p a.1).world) aL x = o := by simpa only [hw] using ho
  constructor
  · have hparent := hknown a x hx
    rwa [ho', hw] at hparent
  · rcases hold a.1 with ⟨_, _, _, _, _, _, _, _, _, _, hinc, _⟩
    have ht := (hinc x hxold).2.2.1
    have hend : (((p a.1).timeIndex : ℝ) + 1) / (2 : ℝ) ^ T =
        (p a.1).start + ((2 : ℝ) ^ T)⁻¹ := by unfold StripParent.start; ring
    have ht' : x.2 ∈ Set.Icc (p a.1).start ((p a.1).start + ((2 : ℝ) ^ T)⁻¹) := by
      constructor
      · exact ht.1
      · rw [← hend]
        exact ht.2
    have hvel := (mergedStripCell_velocity_bound hr (by linarith)
      (hV _ _ hx.1.2.1.1) hx.1.2.1.2).trans hwidth
    have h := packet_midpoint_bin_known_of_obs_eq
      (p a.1).frame (p a.1).center (p a.1).velocity
      (d.normal a.1 (canonicalStripIndex d.radius (d.normal a.1) (d.offset a.1) a.2.1))
      (B (p a.1).world) aL (p a.1).start (((2 : ℝ) ^ T)⁻¹)
      d.radius (d.offset a.1 (canonicalStripIndex d.radius (d.normal a.1) (d.offset a.1) a.2.1))
      d.normalBudget x o (by positivity) hr ht' hvel ho'
    rw [hx.1.2.2] at h
    exact h

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
