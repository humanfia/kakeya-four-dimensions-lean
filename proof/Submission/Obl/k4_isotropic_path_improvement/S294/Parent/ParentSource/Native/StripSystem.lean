-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripSystem, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripSystem.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripSystem.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripSystem.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripSystem.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Common
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMultiplicity

/-! A concrete strip cover with original mass gives the frozen width system.
All geometric, format, list and mass requirements remain explicit. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

namespace StripParent

open Classical in
theorem system_of_finite_family {α : Type} [Fintype α] {W T Mi Di : ℕ}
    {N L depth τ : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (p : α → StripParent W T) (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (hcard : (Fintype.card α : ℝ) ≤ N ^ Mi)
    (hdisj : ∀ b b', b ≠ b' → (p b).world = (p b').world →
      (p b).timeIndex = (p b').timeIndex → Disjoint (p b).trajectories (p b').trajectories)
    (hmult : ∀ γ o, ((Finset.univ.filter (fun b => (p b).world = γ ∧
      ∃ x ∈ (p b).incidences, gobs (B γ) (gδ N L) x = o)).card : ℝ) ≤ N ^ τ)
    (hchart : ∀ b, (p b).Valid N Mi Di (N ^ τ) depth B E)
    (hextra : ∀ b, extra (p b).frame)
    (hmass : ENNReal.ofReal (N ^ (-τ)) ≤
      ∑ b, ENNReal.ofReal (ω (p b).world) * (ν (p b).world).prod volume (p b).incidences) :
    system N L W ω ν E B Mi Di τ depth T extra := by
  let e := Fintype.equivFin α
  let lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin (Fintype.card α)) :=
    fun γ o => (Finset.univ.filter (fun b => (p b).world = γ ∧
      ∃ x ∈ (p b).incidences, gobs (B γ) (gδ N L) x = o)).map e.toEmbedding
  refine ⟨Fintype.card α, (fun b => (p (e.symm b)).world),
    (fun b => (p (e.symm b)).timeIndex), (fun b => (p (e.symm b)).center),
    (fun b => (p (e.symm b)).velocity), (fun b => (p (e.symm b)).frame),
    (fun b => (p (e.symm b)).test), (fun b => (p (e.symm b)).trajectories),
    (fun b => (p (e.symm b)).incidences), lst, hcard, ?_, ?_, ?_, ?_⟩
  · intro b b' hne hw ht
    exact hdisj _ _ (fun h => hne (e.symm.injective h)) hw ht
  · intro γ o
    simpa only [lst, Finset.card_map] using hmult γ o
  · intro b
    refine ⟨?_, hextra (e.symm b)⟩
    rcases hchart (e.symm b) with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ?_⟩
    intro x hx
    apply Finset.mem_map.mpr
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, x, hx, rfl⟩
  · exact hmass.trans_eq (Fintype.sum_equiv e.symm
      (fun b : Fin (Fintype.card α) => ENNReal.ofReal (ω (p (e.symm b)).world) *
        (ν (p (e.symm b)).world).prod volume (p (e.symm b)).incidences)
      (fun b : α => ENNReal.ofReal (ω (p b).world) *
        (ν (p b).world).prod volume (p b).incidences) (fun _ => rfl)).symm

end StripParent

namespace StripRefinement

open Classical in
/-- Every explicit strip-cover certificate, including its original mass floor,
produces an admissible old-level system with any verified frame improvement. -/
theorem system_of_cover {α : Type} [Fintype α] {W T : ℕ}
    (d : StripRefinement α) (p : α → StripParent W T)
    {N L κ depth τ : ℝ} {M M' D : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {B : Fin W → ℝ} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    (hold : ∀ b, (p b).Valid N M D κ depth B E) (hN : 1 ≤ N) (hM : M ≤ M')
    (hκ : 1 ≤ κ) (hκτ : κ ≤ N ^ τ) (hslack : 4 ≤ N ^ τ) (hB : ∀ w, 0 ≤ B w)
    (hr : 0 < d.radius)
    (he : ∀ b i, ‖d.tangent b i‖ = 1) (hn : ∀ b i, ‖d.normal b i‖ = 1)
    (hen : ∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0)
    (hbins : κ ≤ (d.bins : ℝ) * d.radius)
    (hformat : 2 * N ^ M + 2 * (d.count : ℝ) + 2 ≤ N ^ M')
    (hcard : (Fintype.card α * (d.count * (2 * d.bins + 1)) : ℝ) ≤ N ^ M')
    (hdata : ∀ a : d.Label,
      ‖d.center p a‖ + ‖d.velocity p a‖ ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, (|d.frame p κ a i j| + |(d.frame p κ a)⁻¹ i j|)) ≤ N ^ M' ∧
      (∑ i : Fin 2, ∑ j : Fin 2, |d.frame p κ a i j|) ≤ N ^ τ / (2 : ℝ) ^ T)
    (hdisj : ∀ b b', b ≠ b' → (p b).world = (p b').world →
      (p b).timeIndex = (p b').timeIndex → Disjoint (p b).trajectories (p b').trajectories)
    (oldList : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset α)
    (hknown : ∀ b x, x ∈ (p b).incidences →
      b ∈ oldList (p b).world (gobs (B (p b).world) (gδ N L) x))
    (hlist : ∀ γ o,
      ((oldList γ o).card * (d.count * (2 * d.normalBudget + 1)) : ℝ) ≤ N ^ τ)
    (extra : Matrix (Fin 2) (Fin 2) ℝ → Prop)
    (hextra : ∀ a : d.Label, extra (d.frame p κ a))
    (hmass : ENNReal.ofReal (N ^ (-τ)) ≤
      ∑ b, ENNReal.ofReal (ω (p b).world) *
        (ν (p b).world).prod volume (d.coveredIncidences p b)) :
    system N L W ω ν E B M' (max D 1) τ depth T extra := by
  apply StripParent.system_of_finite_family (d.refinedParent p κ) extra
  · simpa only [d.label_card, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hcard
  · intro a a' hne hw ht
    exact d.assignment_disjoint p hdisj hne hw ht
  · intro γ o
    have h : ((Finset.univ.filter (fun a : d.Label => (p a.1).world = γ ∧
        ∃ x ∈ d.incidence p a, gobs (B γ) (gδ N L) x = o)).card : ℝ) ≤
        (oldList γ o).card * (d.count * (2 * d.normalBudget + 1)) := by
      exact_mod_cast d.observation_multiplicity p hold hr oldList hknown γ o
    exact h.trans (hlist γ o)
  · exact d.valid p hold hN hM hκ hκτ hslack hB hr he hn hen hformat hdata
  · exact hextra
  · exact hmass.trans_eq (d.sum_weighted_incidence p hold hr hn hbins ω
      (fun w => (ν w).prod volume)).symm

end StripRefinement

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
