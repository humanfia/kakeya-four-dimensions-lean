-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.DensePackets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/DensePackets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/DensePackets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/DensePackets.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PathFacts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketTransfer
import Submission.Obl.k4_quadratic_finite_greedy_cover.PacketBudget

/-!
# Dense packets under the original mixture

The unit budget for full packets permits a relative-mass pigeonhole without
paying for the number of worlds or packets. Selected worlds have positive
original weight. No law is restricted or normalized in this step.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

/-- A finite cover may be summed with its original world weights; the counted
pieces keep their intersection with the original residual. -/
theorem weighted_cover_mass_le {X Γ I : Type*} [MeasurableSpace X]
    [Fintype Γ] [Fintype I] (μ : Γ → Measure X) (w : Γ → ENNReal)
    (γ : I → Γ) (F : I → Set X) (H : Γ → Set X)
    (hcover : ∀ g, H g ⊆ {p | ∃ b, γ b = g ∧ p ∈ F b}) :
    (∑ g, w g * μ g (H g)) ≤ ∑ b, w (γ b) * μ (γ b) (H (γ b) ∩ F b) := by
  classical
  have hlocal (g : Γ) : μ g (H g) ≤
      ∑ b, if γ b = g then μ g (H g ∩ F b) else 0 := by
    have hsub : H g ⊆ ⋃ b, if γ b = g then H g ∩ F b else ∅ := by
      intro p hp
      obtain ⟨b, hbg, hpb⟩ := hcover g hp
      exact mem_iUnion.mpr ⟨b, by simpa only [hbg, ite_true, mem_inter_iff] using And.intro hp hpb⟩
    refine (measure_mono hsub).trans ?_
    simpa only [apply_ite, measure_empty] using
      measure_iUnion_fintype_le (μ g) (fun b => if γ b = g then H g ∩ F b else ∅)
  calc
    _ ≤ ∑ g, w g * ∑ b, if γ b = g then μ g (H g ∩ F b) else 0 :=
      Finset.sum_le_sum (fun g _ => mul_le_mul' le_rfl (hlocal g))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp [mul_ite, eq_comm]

/-- A unit total capacity and positive residual mass select a packet with the
same relative mass. In particular its original world weight is positive. -/
theorem exists_dense_packet_of_unit_budget {X Γ I : Type*} [MeasurableSpace X]
    [Fintype Γ] [Fintype I] (μ : Γ → Measure X) (w : Γ → ℝ)
    (γ : I → Γ) (packet counted : I → Set X) {α : ℝ}
    (hα : 0 < α) (hfinite : ∀ b, μ (γ b) (packet b) ≠ ∞)
    (hsub : ∀ b, counted b ⊆ packet b)
    (hmass : ENNReal.ofReal α ≤
      ∑ b, ENNReal.ofReal (w (γ b)) * μ (γ b) (counted b))
    (hbudget : (∑ b, ENNReal.ofReal (w (γ b)) * μ (γ b) (packet b)) ≤ 1) :
    ∃ b, 0 < w (γ b) ∧ μ (γ b) (packet b) ≠ 0 ∧
      ENNReal.ofReal α * μ (γ b) (packet b) ≤ μ (γ b) (counted b) := by
  classical
  obtain ⟨b, _, hpos, hratio⟩ := exists_packet_of_capacity_bound_ennreal
    Finset.univ
    (fun b => ENNReal.ofReal (w (γ b)) * μ (γ b) (packet b))
    (fun b => ENNReal.ofReal (w (γ b)) * μ (γ b) (counted b))
    (reference := 1) (α := α) (β := 1) (by norm_num) (by norm_num) hα
    (by norm_num)
    (fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite b))
    (fun b _ => mul_le_mul' le_rfl (measure_mono (hsub b)))
    (by simpa using hmass) (by simpa using hbudget)
  have hw : ENNReal.ofReal (w (γ b)) ≠ 0 := (mul_ne_zero_iff.mp hpos).1
  refine ⟨b, ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hw),
    (mul_ne_zero_iff.mp hpos).2, ?_⟩
  have hr : ENNReal.ofReal (w (γ b)) * (ENNReal.ofReal α * μ (γ b) (packet b)) ≤
      ENNReal.ofReal (w (γ b)) * μ (γ b) (counted b) := by
    simpa only [div_one, mul_left_comm] using hratio
  apply (ENNReal.mul_le_mul_iff_left hw ENNReal.ofReal_ne_top).mp
  simpa only [mul_comm] using hr

section Path

variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ}
    {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ} {par : Fin C → Fin C}
    {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Event}
    {lst : ℕ → Fin W → BaseObservation → Finset (Fin C)}
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ
      C lev par γ j c u Q R A F lst)

include hp

/-- At every earlier level a residual of original mixture mass at least `α`
contains a packet at relative mass at least `α`. No factor for the number of
path cells is lost, and the selected world's original weight is positive. -/
theorem path_exists_dense_packet
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : ∑ w, ω w = 1)
    (H : Fin W → Set Event)
    (hH : ∀ w, H w ⊆ {p | ∃ b, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b})
    {α : ℝ} (hα : 0 < α)
    (hmass : ENNReal.ofReal α ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w))
    (i : ℕ) (hi : i < m) :
    ∃ b : Fin C, lev b = i ∧ 0 < ω (γ b) ∧ ν (γ b) (A b) ≠ 0 ∧
      ENNReal.ofReal (α / (2 : ℝ) ^ T i) * ν (γ b) (A b) ≤
        (ν (γ b)).prod volume (H (γ b) ∩ F b) := by
  classical
  let I := {b : Fin C // lev b = i}
  let full : I → Set Event := fun b =>
    A b.val ×ˢ Icc ((j b.val : ℝ) / (2 : ℝ) ^ T i)
      (((j b.val : ℝ) + 1) / (2 : ℝ) ^ T i)
  let counted : I → Set Event := fun b => H (γ b.val) ∩ F b.val
  have hfull (b : I) : (ν (γ b.val)).prod volume (full b) =
      ν (γ b.val) (A b.val) * ENNReal.ofReal (1 / (2 : ℝ) ^ T i) := by
    dsimp only [full]
    rw [Measure.prod_prod, Real.volume_Icc]
    congr 2
    ring
  have hfinite (b : I) : (ν (γ b.val)).prod volume (full b) ≠ ∞ := by
    have := hν (γ b.val)
    rw [hfull]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hsub (b : I) : counted b ⊆ full b := by
    intro p h
    have hs := path_packet_support hp b.val h.2
    exact ⟨hs.2.1, by simpa only [b.property] using hs.2.2.1⟩
  have hbudget : (∑ b : I, ENNReal.ofReal (ω (γ b.val)) *
      (ν (γ b.val)).prod volume (full b)) ≤ 1 := by
    apply k4_quadratic_finite_greedy_cover.full_packet_mass_le_one
      W ν ω (fun b : I => γ b.val) (fun b : I => j b.val) (T i)
      (fun b : I => A b.val) hν hω hωsum
      (fun b => (path_packet_measurable hp b.val).1)
    · intro b
      simpa only [b.property] using (hp.2.2.2.2.2.2.2 b.val).2.1
    · intro b b' hne hγ hj
      apply hp.2.2.2.2.2.2.1 b.val b'.val
      · exact fun h => hne (Subtype.ext h)
      · exact b.property.trans b'.property.symm
      · exact hγ
      · exact hj
  have hcover (w : Fin W) : H w ⊆ {p | ∃ b : I, γ b.val = w ∧ p ∈ F b.val} := by
    intro p h
    obtain ⟨b, hb, hbw, hpb⟩ := path_residual_level_cover hp hH i hi w h
    exact ⟨⟨b, hb⟩, hbw, hpb⟩
  have hm := weighted_cover_mass_le (fun w => (ν w).prod volume)
    (fun w => ENNReal.ofReal (ω w)) (fun b : I => γ b.val)
    (fun b : I => F b.val) H hcover
  obtain ⟨b, hw, hbpos, hratio⟩ := exists_dense_packet_of_unit_budget
    (fun w => (ν w).prod volume) ω (fun b : I => γ b.val) full counted hα
    hfinite hsub (hmass.trans hm) hbudget
  have hApos : ν (γ b.val) (A b.val) ≠ 0 := by
    rw [hfull] at hbpos
    exact (mul_ne_zero_iff.mp hbpos).1
  refine ⟨b.val, b.property, hw, hApos, ?_⟩
  rw [hfull] at hratio
  have heq : ENNReal.ofReal (α / (2 : ℝ) ^ T i) * ν (γ b.val) (A b.val) =
      ENNReal.ofReal α * (ν (γ b.val) (A b.val) *
        ENNReal.ofReal (1 / (2 : ℝ) ^ T i)) := by
    rw [div_eq_mul_one_div, ENNReal.ofReal_mul hα.le]
    ac_rfl
  rw [heq]
  exact hratio

/-- The residual floor in the frozen discovery statement gives the same
relative floor in a positive-weight packet at any specified earlier level. -/
theorem path_exists_dense_residual_packet
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hωsum : ∑ w, ω w = 1)
    (H : Fin W → Set Event)
    (hH : ∀ w, H w ⊆ {p | ∃ b, lev b = m - 1 ∧ γ b = w ∧ p ∈ F b})
    (hmass : ENNReal.ofReal (κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w))
    (i : ℕ) (hi : i < m) :
    ∃ b : Fin C, lev b = i ∧ 0 < ω (γ b) ∧ ν (γ b) (A b) ≠ 0 ∧
      ENNReal.ofReal ((κ⁻¹ / 2) / (2 : ℝ) ^ T i) * ν (γ b) (A b) ≤
        (ν (γ b)).prod volume (H (γ b) ∩ F b) := by
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one hp.1
  exact path_exists_dense_packet hp hν hω hωsum H hH (by positivity) hmass i hi

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
