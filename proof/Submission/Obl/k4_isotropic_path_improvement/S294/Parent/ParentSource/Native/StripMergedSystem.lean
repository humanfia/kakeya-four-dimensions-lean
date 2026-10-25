-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedSystem, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedSystem.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedSystem.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedSystem.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedSystem.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedMultiplicity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSystem

/-! The merged parameter-bin atlas gives the frozen width system. Net size
enters the polynomial chart count and Boolean format; its observation budget
uses only the original predicted parameter list. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

namespace StripRefinement

open Classical in
theorem system_of_merged_family {α : Type} [Fintype α] {W T : ℕ}
    (d : StripRefinement α) (p : α → StripParent W T)
    {N L κ depth τ w Hs : ℝ} {M M' D Ds : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hN : 1 ≤ N) (hM : M ≤ M')
    (hκ : 1 ≤ κ) (hκτ : κ ≤ N ^ τ) (hslack : 4 ≤ N ^ τ) (hB : ∀ w, 0 ≤ B w)
    (hr : 0 < d.radius)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (hV : ∀ b l, l ∈ (p b).trajectories →
      ‖packetVelocity (((2 : ℝ) ^ T)⁻¹) (p b).frame (p b).velocity l‖ ≤ 2 * κ)
    (hwidth : w + 3 * (1 + 2 * κ) * d.radius ≤ (d.normalBudget : ℝ) * d.radius)
    (success : α → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hSmeas : ∀ b q, MeasurableSet (success b q)) (hHs : 0 ≤ Hs)
    (hS : ∀ b q copy, gfmt 7 Hs Ds
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ success b q})
    (hformat : 2 * N ^ M + 2 * (d.count : ℝ) + 2 + Hs ≤ N ^ M')
    (hcard : (Fintype.card α * (d.count * (2 * d.bins + 1)) : ℝ) ≤ N ^ M')
    (hdata : ∀ a : d.Label,
      ‖d.center p a‖ + ‖d.velocity p a‖ ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, (|d.frame p κ a i j| + |(d.frame p κ a)⁻¹ i j|)) ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |d.frame p κ a i j|) ≤ N ^ τ / (2 : ℝ) ^ T)
    (hdisj : ∀ b b', b ≠ b' → (p b).world = (p b').world →
      (p b).timeIndex = (p b').timeIndex → Disjoint (p b).trajectories (p b').trajectories)
    (paramList : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset d.MergedParameterLabel)
    (hknown : ∀ a x, x ∈ d.mergedIncidence p w success a →
      d.mergedParameterLabel a ∈
        paramList (p a.1).world (gobs (B (p a.1).world) (gδ N L) x))
    (hlist : ∀ γ o, ((paramList γ o).card * (2 * d.normalBudget + 1) : ℝ) ≤ N ^ τ)
    (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (hextra : ∀ a : d.Label, extra (d.frame p κ a))
    (hmass : ENNReal.ofReal (N ^ (-τ)) ≤
      ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p a.1).world) *
        (ν (p a.1).world).prod volume (d.mergedIncidence p w success a)) :
    system N L W ω ν E B M' (max (max D 1) Ds) τ depth T extra := by
  apply StripParent.system_of_finite_family (d.mergedParent p κ w success) extra
  · have hc : (Fintype.card d.MergedLabel : ℝ) ≤
        (Fintype.card α * (d.count * (2 * d.bins + 1)) : ℕ) := by
      exact_mod_cast d.mergedLabel_card_le
    exact hc.trans (by exact_mod_cast hcard)
  · intro a a' hne hw ht
    exact d.mergedAssignment_disjoint p w hdisj hne hw ht
  · intro γ o
    have h : ((Finset.univ.filter (fun a : d.MergedLabel => (p a.1).world = γ ∧
        ∃ x ∈ d.mergedIncidence p w success a, gobs (B γ) (gδ N L) x = o)).card : ℝ) ≤
        (paramList γ o).card * (2 * d.normalBudget + 1) := by
      exact_mod_cast d.merged_observation_multiplicity p hold hr hκ hV hwidth
        success paramList hknown γ o
    exact h.trans (hlist γ o)
  · exact d.merged_valid p hold hN hM hκ hκτ hslack hB hr he hn hen hV hwidth
      success hSmeas hHs hS hformat hdata
  · intro a
    exact hextra (d.mergedCanonicalLabel a)
  · exact hmass

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
