-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FullDensity, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FullDensity.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FullDensity.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FullDensity.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Partitions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.MassPruning

/-! A substantial original residual can be restricted to actual fine packets
which are dense relative to their full ORIGINAL assignment times block length.
The loss is a fixed factor, with no packet-count factor or new denominator. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.exists_full_dense_residual
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w) (hsum : ∑ w, ω w = 1)
    (J : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hJ : ∀ w, MeasurableSet (J w))
    (hcover : ∀ w, J w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) {α : ℝ} (hα : 0 ≤ α)
    (hmass : ENNReal.ofReal α ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (J w)) :
    ∃ J' : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (J' w)) ∧ (∀ w, J' w ⊆ J w) ∧
      ENNReal.ofReal (α / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (J' w) ∧
      ∀ w x, x ∈ J' w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧
        ENNReal.ofReal ((α / 2) / (2 : ℝ) ^ p.T i) * ν (p.γ b) (p.A b) ≤
          ((ν (p.γ b)).prod volume) (J (p.γ b) ∩ p.F b) := by
  classical
  let weight : Fin p.C → ENNReal := fun b =>
    if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) else 0
  let reference : Fin p.C → ENNReal := fun b =>
    ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)
  let selected : Fin p.C → ENNReal := fun b =>
    ((ν (p.γ b)).prod volume) (J (p.γ b) ∩ p.F b)
  let ids := Finset.univ.filter (fun b => p.lev b = i ∧
    ENNReal.ofReal (α / 2) * reference b ≤ selected b)
  let D := fun b => J (p.γ b) ∩ p.F b
  let J' := fun w => {x | ∃ b ∈ ids, p.γ b = w ∧ x ∈ D b}
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hD (b : Fin p.C) : MeasurableSet (D b) := (hJ _).inter (hF b)
  have hmeas (w : Fin W) : MeasurableSet (J' w) := by
    have heq : J' w = ⋃ b : Fin p.C, if b ∈ ids ∧ p.γ b = w then D b else ∅ := by
      ext x
      simp only [J', mem_ofPred_eq, mem_iUnion]
      aesop
    rw [heq]
    apply MeasurableSet.iUnion
    intro b
    split
    · exact hD b
    · exact MeasurableSet.empty
  have hmass' : ENNReal.ofReal α ≤ ∑ b, weight b * selected b := by
    have heq := hp.residual_mass_eq_sum J hJ hcover i hi
    simpa only [weight, selected, ite_mul, zero_mul] using hmass.trans_eq heq
  have hheavy := heavy_packet_mass_ge_half weight reference selected hα
    (hp.full_reference_mass_le_one hν hω hsum i) hmass'
  have hpacketSum := weighted_packet_union_mass (fun w => (ν w).prod volume)
    (fun w => ENNReal.ofReal (ω w)) p.γ D ids (fun b _ => hD b) (by
      intro b hb b' hb' hne hγ
      have hbi := (Finset.mem_filter.mp hb).2.1
      have hb'i := (Finset.mem_filter.mp hb').2.1
      exact (hp.packet_aedisjoint b b' hne (hbi.trans hb'i.symm) hγ).mono
        inter_subset_right inter_subset_right)
  have hsum' : (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (J' w)) =
      ∑ b, if ENNReal.ofReal (α / 2) * reference b ≤ selected b then weight b * selected b else 0 := by
    rw [hpacketSum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hbi : p.lev b = i <;>
      by_cases hdense : ENNReal.ofReal (α / 2) * reference b ≤ selected b <;>
      simp only [ids, weight, selected, D, hbi, hdense, and_self, and_false, false_and,
        ite_true, ite_false, zero_mul]
  refine ⟨J', hmeas, ?_, by simpa only [hsum'] using hheavy, ?_⟩
  · intro w x hx
    obtain ⟨b, _, hbγ, hxb⟩ := hx
    simpa only [hbγ] using hxb.1
  · intro w x hx
    obtain ⟨b, hb, hbγ, hxb⟩ := hx
    obtain ⟨hbi, hbfloor⟩ := (Finset.mem_filter.mp hb).2
    refine ⟨b, hbi, hbγ, hxb.2, ?_⟩
    change ENNReal.ofReal (α / 2) *
      (ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)) ≤ _ at hbfloor
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hbfloor
    simpa only [div_eq_mul_inv] using hbfloor

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
