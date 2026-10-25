-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripCover, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripCover.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripCover.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripCover.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripCover.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripInfinitePacking
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripParameterBins

/-! Uniformly indexed covers of arbitrary heavy-strip families under one fixed
probability palette per parent. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace BigOperators

def stripTangent (n : StripSpace) : StripSpace := WithLp.toLp 2 ![-n 1, n 0]

theorem stripTangent_norm (n : StripSpace) : ‖stripTangent n‖ = ‖n‖ := by
  have h : ‖stripTangent n‖ ^ 2 = n 1 ^ 2 + n 0 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [stripTangent, Fin.sum_univ_two]
  have h' : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq n
  nlinarith [norm_nonneg (stripTangent n), norm_nonneg n]

theorem stripTangent_inner (n : StripSpace) : inner ℝ (stripTangent n) n = 0 := by
  simp [stripTangent, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem boundedStrip_offset_le {n x : StripSpace} {β r T : ℝ}
    (hn : ‖n‖ = 1) (hx : x ∈ boundedStrip n β r T) : |β| ≤ T + r := by
  have hnorm : ‖x‖ ≤ T := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
  have hi : |inner ℝ x n| ≤ T :=
    (abs_real_inner_le_norm _ _).trans (by simpa only [hn, mul_one] using hnorm)
  have h : |β| ≤ |β - inner ℝ x n| + |inner ℝ x n| := by
    simpa only [sub_add_cancel] using abs_add_le (β - inner ℝ x n) (inner ℝ x n)
  rw [abs_sub_comm] at h
  have hs : |inner ℝ x n - β| ≤ r := hx.2
  exact h.trans (by linarith)

theorem boundedStrip_offset_le_of_heavy (μ : Measure StripSpace)
    {n : StripSpace} {β r T κ : ℝ} (hn : ‖n‖ = 1) (hκ : 0 < κ)
    (hmass : κ ≤ μ.real (boundedStrip n β r T)) : |β| ≤ T + r := by
  have hne : (boundedStrip n β r T).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measureReal_def, measure_empty,
      ENNReal.toReal_zero] at hmass
    linarith
  obtain ⟨x, hx⟩ := hne
  exact boundedStrip_offset_le hn hx

/-- The list length is uniform in the parent, with no finiteness assumption
on the predicted states. Padding adds harmless zero-offset unit strips. -/
theorem exists_uniform_heavy_strip_parameter_net_of_active {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    (hprob : ∀ b, Nonempty (ι b) → IsProbabilityMeasure (μ b))
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {κ ε r ρ T : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hκ : 0 < κ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ b i, κ ≤ (μ b).real (boundedStrip (n b i) (β b i) r T))
    (hcap : ∀ b, Nonempty (ι b) → ∀ x,
      (μ b) (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ (C : ℕ) (n' : P → Fin C → StripSpace) (β' : P → Fin C → ℝ),
      0 < C ∧ (C : ℝ) ≤ 2 / κ ^ 2 + 1 ∧
      (∀ b i, ‖n' b i‖ = 1) ∧ (∀ b i, |β' b i| ≤ T + r) ∧
      ∀ b i, ∃ j, stripParametersClose (n b i) (β b i) (n' b j) (β' b j) ρ := by
  classical
  have hex (b : P) : ∃ s : Finset (ι b), (s.card : ℝ) ≤ 2 / κ ^ 2 ∧
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ρ ≤ ‖n b i - n b j‖ + |β b i - β b j| ∧
          ρ ≤ ‖n b i + n b j‖ + |β b i + β b j|) ∧
      ∀ i, ∃ j ∈ s,
        ‖n b i - n b j‖ + |β b i - β b j| < ρ ∨
          ‖n b i + n b j‖ + |β b i + β b j| < ρ := by
    by_cases hb : Nonempty (ι b)
    · haveI := hprob b hb
      exact exists_short_heavy_strip_net_unrestricted (μ b) (n b) (β b) (hn b)
        hκ hε hT hρ hsmall (hmass b) (hcap b hb) heps
    · exact ⟨∅, by simp only [Finset.card_empty, Nat.cast_zero]; positivity,
        by simp, fun i => False.elim (hb ⟨i⟩)⟩
  choose s hs using hex
  let C : ℕ := ⌈2 / κ ^ 2⌉₊
  have hC : 0 < C := Nat.one_le_ceil_iff.mpr (by positivity)
  have hcard (b : P) : (s b).card ≤ C := by
    exact_mod_cast (hs b).1.trans (Nat.le_ceil (2 / κ ^ 2))
  let e (b : P) := Fintype.equivFin {i : ι b // i ∈ s b}
  let n₀ : StripSpace := WithLp.toLp 2 ![(1 : ℝ), 0]
  have hn₀ : ‖n₀‖ = 1 := by
    have h : ‖n₀‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [n₀, Fin.sum_univ_two]
    nlinarith [norm_nonneg n₀]
  let n' (b : P) (j : Fin C) : StripSpace :=
    if hj : j.val < (s b).card then
      n b ((e b).symm ⟨j.val, by simpa only [Fintype.card_coe] using hj⟩).val else n₀
  let β' (b : P) (j : Fin C) : ℝ :=
    if hj : j.val < (s b).card then
      β b ((e b).symm ⟨j.val, by simpa only [Fintype.card_coe] using hj⟩).val else 0
  refine ⟨C, n', β', hC, (Nat.ceil_lt_add_one (by positivity)).le, ?_, ?_, ?_⟩
  · intro b j
    dsimp only [n']
    split_ifs with hj
    · exact hn _ _
    · exact hn₀
  · intro b j
    dsimp only [β']
    split_ifs with hj
    · exact boundedStrip_offset_le_of_heavy (μ b) (hn _ _) hκ (hmass _ _)
    · simpa only [abs_zero] using add_nonneg hT hr
  · intro b i
    obtain ⟨i', hi', hclose⟩ := (hs b).2.2 i
    let z : {i : ι b // i ∈ s b} := ⟨i', hi'⟩
    let j : Fin C := ⟨((e b) z).val, (by
      have h : ((e b) z).val < (s b).card := by
        simpa only [Fintype.card_coe] using ((e b) z).isLt
      exact h.trans_le (hcard b))⟩
    have hj : j.val < (s b).card := by
      simpa only [j, Fintype.card_coe] using ((e b) z).isLt
    have heval : (e b).symm ⟨j.val, by simpa only [Fintype.card_coe] using hj⟩ = z := by
      apply (e b).injective
      simpa only [Equiv.apply_symm_apply] using (Fin.ext rfl :
        (⟨j.val, by simpa only [Fintype.card_coe] using hj⟩ : Fin (Fintype.card {i : ι b // i ∈ s b})) =
          (e b) z)
    refine ⟨j, ?_⟩
    simp only [n', β', dite_eq_left hj, heval]
    exact hclose.imp le_of_lt le_of_lt

theorem exists_uniform_heavy_strip_cover_of_active {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    (hprob : ∀ b, Nonempty (ι b) → IsProbabilityMeasure (μ b))
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {κ ε r ρ T : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hκ : 0 < κ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ b i, κ ≤ (μ b).real (boundedStrip (n b i) (β b i) r T))
    (hcap : ∀ b, Nonempty (ι b) → ∀ x,
      (μ b) (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ (C : ℕ) (n' : P → Fin C → StripSpace) (β' : P → Fin C → ℝ),
      0 < C ∧ (C : ℝ) ≤ 2 / κ ^ 2 + 1 ∧
      (∀ b i, ‖n' b i‖ = 1) ∧ (∀ b i, |β' b i| ≤ T + r) ∧
      ∀ b i x, ‖x‖ ≤ T → x ∈ affineStrip (n b i) (β b i) r →
        x ∈ ⋃ j, affineStrip (n' b j) (β' b j) (r + (1 + T) * ρ) := by
  obtain ⟨C, n', β', hC, hcard, hn', hβ', hcover⟩ :=
    exists_uniform_heavy_strip_parameter_net_of_active μ hprob n β hn hκ hε hr hT
      hρ hsmall hmass hcap heps
  refine ⟨C, n', β', hC, hcard, hn', hβ', ?_⟩
  intro b i x hx hxi
  obtain ⟨j, hj⟩ := hcover b i
  exact Set.mem_iUnion.mpr ⟨j,
    affineStrip_mem_of_close_parameters_mod_sign hT hx hj hxi⟩

theorem exists_uniform_heavy_strip_cover {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    [∀ b, IsProbabilityMeasure (μ b)]
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {κ ε r ρ T : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hκ : 0 < κ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ b i, κ ≤ (μ b).real (boundedStrip (n b i) (β b i) r T))
    (hcap : ∀ b x, (μ b) (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ (C : ℕ) (n' : P → Fin C → StripSpace) (β' : P → Fin C → ℝ),
      0 < C ∧ (C : ℝ) ≤ 2 / κ ^ 2 + 1 ∧
      (∀ b i, ‖n' b i‖ = 1) ∧ (∀ b i, |β' b i| ≤ T + r) ∧
      ∀ b i x, ‖x‖ ≤ T → x ∈ affineStrip (n b i) (β b i) r →
        x ∈ ⋃ j, affineStrip (n' b j) (β' b j) (r + (1 + T) * ρ) :=
  exists_uniform_heavy_strip_cover_of_active μ (fun _ _ => inferInstance) n β
    hn hκ hε hr hT hρ hsmall hmass (fun b _ => hcap b) heps

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
