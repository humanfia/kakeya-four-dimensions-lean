-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PathAngularLoss, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PathAngularLoss.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PathAngularLoss.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PathAngularLoss.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PathAngularCut
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.AngularPreparationLoss

/-! Explicit original mass loss for the actual path angular masks. The
parent references are unchanged. This refines the half-mass wrapper in
Native.PathAngularCut, adapted there from LOT o116/x0389/e3859a9b. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

theorem ProblemData.Valid.prepare_path_angular_cut_of_list_loss {T : Type*}
    {d : ProblemData} (hd : d.Valid) (k : ℕ) (p : PathData (d.W k))
    (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (u : T → ℝ) (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ : ℝ) (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hH : ∀ w, MeasurableSet (H w)) (hHE : ∀ w, H w ⊆ d.E k w)
    (lst : Fin (d.W k) → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin p.C))
    (hlist : ∀ w o, ((lst w o).card : ℝ) ≤ m * p.κ)
    (hknown : ∀ w b q, q ∈ H w ∩ (if p.γ b = w then p.F b else ∅) →
      b ∈ lst w (obs (d.B k w) (δ (d.N k) d.L) q))
    (hpure : ∀ w q, q ∈ H w → ENNReal.ofReal (d.N k ^ (-d.f d.L - τ)) ≤
      d.g k w d.L (obs (d.B k w) (δ (d.N k) d.L) q))
    (hangular : ∀ t w q, q ∈ H w →
      d.G k w (u t) (d.angularObs (u t) k w q) ≤
        ENNReal.ofReal (d.N k ^ (-d.f d.L - d.S * u t + τ)))
    (ε : ENNReal) (hε : ε ≠ 0) (hεtop : ε ≠ ∞) :
    ∃ A : Fin (d.W k) → Fin p.C → Set (EuclideanSpace ℝ (Fin 3) × ℤ),
      (∀ w b, MeasurableSet (A w b)) ∧
      (∀ w, MeasurableSet (d.pathAngularCut k p H A w) ∧ d.pathAngularCut k p H A w ⊆ H w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w)) ≤
        (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (d.pathAngularCut k p H A w)) +
          ε * ENNReal.ofReal (m * p.κ) ∧
      (∀ b, (d.μ k (p.γ b)).restrict (d.pathAngularCut k p H A (p.γ b) ∩ p.F b) ≤
        d.pathAngularReference k p H A b) ∧
      ∀ t b i, d.pathAngularReference k p H A b
        {q | (fun j => ⌊v q.1 j / δ (d.N k) (u t)⌋) = i} ≤
          (ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) * ε⁻¹) *
            d.pathAngularReference k p H A b univ := by
  classical
  have hE (w : Fin (d.W k)) (b : Fin p.C) :
      MeasurableSet (d.pathPacketEvents k p H w b) := by
    apply (hH w).inter
    split
    · exact (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    · exact MeasurableSet.empty
  have hobs (w : Fin (d.W k)) : Measurable (obs (d.B k w) (δ (d.N k) d.L)) :=
    Submission.Obl.k4_dk4_smoothed_problem.Framework.measurable_pureObservation _ _
  have hμH (w : Fin (d.W k)) : d.μ k w (H w) = ((d.ν k w).prod volume) (H w) :=
    d.μ_apply_eq k w (hH w) (hHE w)
  obtain ⟨A, hA, hSmeas, hSH, hSmass, hSdom, hcap⟩ := assemble_weighted_angular_preparation_loss
    (d.μ k) (fun w => ENNReal.ofReal (d.ω k w)) H (d.pathPacketEvents k p H)
    (fun w => obs (d.B k w) (δ (d.N k) d.L))
    (fun _ t q j => ⌊v q.1 j / δ (d.N k) (u t)⌋) hH hE hobs
    (ε * ENNReal.ofReal (m * p.κ))
    (fun _ t => ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) * ε⁻¹)
    (hd.selected_mixture_budget k)
    (fun w => hd.prepare_path_angular_family_of_list k p κ₁ m s δ₀ Mp Dp σ hp u hu τ H hH
      lst hlist hknown hpure hangular ε hε hεtop w)
  refine ⟨A, hA, fun w => ⟨hSmeas w, hSH w⟩, ?_, ?_, ?_⟩
  · have hμS (w : Fin (d.W k)) :
        d.μ k w (observationFamilyCut (H w) (d.pathPacketEvents k p H w)
          (obs (d.B k w) (δ (d.N k) d.L)) (A w)) =
        ((d.ν k w).prod volume) (d.pathAngularCut k p H A w) :=
      d.μ_apply_eq k w (hSmeas w) ((hSH w).trans (hHE w))
    simpa only [hμH, hμS] using hSmass
  · intro b
    have hsub : d.pathAngularCut k p H A (p.γ b) ⊆ H (p.γ b) := hSH (p.γ b)
    have heq : d.pathAngularCut k p H A (p.γ b) ∩ d.pathPacketEvents k p H (p.γ b) b =
        d.pathAngularCut k p H A (p.γ b) ∩ p.F b := by
      rw [pathPacketEvents, ite_eq_left rfl, ← inter_assoc, inter_eq_left.mpr hsub]
    have hh := hSdom (p.γ b) b
    change (d.μ k (p.γ b)).restrict
      (d.pathAngularCut k p H A (p.γ b) ∩ d.pathPacketEvents k p H (p.γ b) b) ≤
        d.pathAngularReference k p H A b at hh
    rw [heq] at hh
    exact hh
  · intro t b i
    exact hcap (p.γ b) t b i


end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
