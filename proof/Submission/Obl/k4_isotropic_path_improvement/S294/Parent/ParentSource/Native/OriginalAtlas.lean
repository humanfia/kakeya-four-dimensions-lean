-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.OriginalAtlas, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/OriginalAtlas.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/OriginalAtlas.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/OriginalAtlas.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedSystem

/- The finite-family assembly generalizes Native.StripSystem and
Native.StripMergedSystem, adapted there from LOT o116/x0389/e3859a9b. -/

/-! Assemble a genuine frozen atlas while keeping arbitrary original-mass
functionals and old-ancestor provenance. The list is constructed from the
actual finite chart family. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

namespace StripParent

open Classical in
theorem atlas_of_finite_family {α : Type} [Fintype α] {W T Mi Di : ℕ}
    {N L depth τ : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (p : α → StripParent W T) (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (aux : Fin W → Fin (2 ^ T) → Set (ℕ × (Fin 6 → ℝ)) →
      Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop)
    (massFloor : ENNReal) (mass : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → ENNReal)
    (hcard : (Fintype.card α : ℝ) ≤ N ^ Mi)
    (hdisj : ∀ b b', b ≠ b' → (p b).world = (p b').world →
      (p b).timeIndex = (p b').timeIndex → Disjoint (p b).trajectories (p b').trajectories)
    (hmult : ∀ w o, ((Finset.univ.filter (fun b => (p b).world = w ∧
      ∃ x ∈ (p b).incidences, gobs (B w) (gδ N L) x = o)).card : ℝ) ≤ N ^ τ)
    (hchart : ∀ b, (p b).Valid N Mi Di (N ^ τ) depth B E)
    (hextra : ∀ b, extra (p b).frame)
    (haux : ∀ b (known : Prop), known →
      aux (p b).world (p b).timeIndex (p b).trajectories (p b).incidences known)
    (hmass : massFloor ≤ ∑ b, ENNReal.ofReal (ω (p b).world) * mass (p b).world (p b).incidences) :
    Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.atlas
      N L W ω ν E B Mi Di τ depth T extra aux massFloor mass := by
  let e := Fintype.equivFin α
  let lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin (Fintype.card α)) :=
    fun w o => (Finset.univ.filter (fun b => (p b).world = w ∧
      ∃ x ∈ (p b).incidences, gobs (B w) (gδ N L) x = o)).map e.toEmbedding
  refine ⟨Fintype.card α, (fun b => (p (e.symm b)).world),
    (fun b => (p (e.symm b)).timeIndex), (fun b => (p (e.symm b)).center),
    (fun b => (p (e.symm b)).velocity), (fun b => (p (e.symm b)).frame),
    (fun b => (p (e.symm b)).test), (fun b => (p (e.symm b)).trajectories),
    (fun b => (p (e.symm b)).incidences), lst, hcard, ?_, ?_, ?_, ?_⟩
  · intro b b' hne hw ht
    exact hdisj _ _ (fun h => hne (e.symm.injective h)) hw ht
  · intro w o
    simpa only [lst, Finset.card_map] using hmult w o
  · intro b
    refine ⟨?_, hextra (e.symm b)⟩
    rcases hchart (e.symm b) with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    apply haux (e.symm b)
    intro x hx
    apply Finset.mem_map.mpr
    exact ⟨e.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, x, hx, rfl⟩,
      e.apply_symm_apply b⟩
  · exact hmass.trans_eq (Fintype.sum_equiv e.symm
      (fun b : Fin (Fintype.card α) => ENNReal.ofReal (ω (p (e.symm b)).world) *
        mass (p (e.symm b)).world (p (e.symm b)).incidences)
      (fun b : α => ENNReal.ofReal (ω (p b).world) * mass (p b).world (p b).incidences)
      (fun _ => rfl)).symm

end StripParent

namespace StripRefinement

open Classical in
theorem atlas_of_merged_family {α : Type} [Fintype α] {W T : ℕ}
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
      d.mergedParameterLabel a ∈ paramList (p a.1).world (gobs (B (p a.1).world) (gδ N L) x))
    (hlist : ∀ w o, ((paramList w o).card * (2 * d.normalBudget + 1) : ℝ) ≤ N ^ τ)
    (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (hextra : ∀ a : d.Label, extra (d.frame p κ a))
    (aux : Fin W → Fin (2 ^ T) → Set (ℕ × (Fin 6 → ℝ)) →
      Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → Prop → Prop)
    (haux : ∀ a : d.MergedLabel, ∀ known : Prop, known → aux (p a.1).world (p a.1).timeIndex
      (d.mergedAssignment p w a) (d.mergedIncidence p w success a) known)
    (massFloor : ENNReal) (mass : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) → ENNReal)
    (hmass : massFloor ≤ ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p a.1).world) *
      mass (p a.1).world (d.mergedIncidence p w success a)) :
    Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.atlas
      N L W ω ν E B M' (max (max D 1) Ds) τ depth T extra aux massFloor mass := by
  apply StripParent.atlas_of_finite_family (d.mergedParent p κ w success) extra aux massFloor mass
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
      exact_mod_cast d.merged_observation_multiplicity p hold hr hκ hV hwidth success paramList hknown γ o
    exact h.trans (hlist γ o)
  · exact d.merged_valid p hold hN hM hκ hκτ hslack hB hr he hn hen hV hwidth
      success hSmeas hHs hS hformat hdata
  · intro a
    exact hextra (d.mergedCanonicalLabel a)
  · exact haux
  · exact hmass

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
