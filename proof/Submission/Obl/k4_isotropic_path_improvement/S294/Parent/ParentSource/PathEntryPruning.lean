-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PathEntryPruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PathEntryPruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PathEntryPruning.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PathEntryPruning.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/PathEntryPruning.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.EntryCompletion
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.DensePackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path

/-! # Heavy local entries under the full original path reference budget -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Remove light local entries BEFORE selecting a common quadratic. Every
surviving assigned point retains the floor of its original unassigned
entry, measured against the full fine assignment and time length. The
global original-mixture loss is at most the entry count times the cutoff. -/
theorem path_heavy_original_entries
    {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hsum : ∑ w, ω w = 1)
    (H : Fin W → Set Event) (hH : ∀ w, MeasurableSet (H w))
    (hterminal : ∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b})
    (i : ℕ) (hi : i < m) (M : ℕ)
    (U : Fin p.C → Fin M → Set Event) (hU : ∀ b e, MeasurableSet (U b e))
    (hsub : ∀ b e, U b e ⊆ H (p.γ b) ∩ p.F b)
    (hcover : ∀ b, p.lev b = i → H (p.γ b) ∩ p.F b ⊆ ⋃ e, U b e)
    (θ : ENNReal) :
    ∃ (V : Fin p.C → Fin M → Set Event) (H' : Fin W → Set Event),
      (∀ b e, MeasurableSet (V b e)) ∧
      (∀ b, Pairwise fun e e' => Disjoint (V b e) (V b e')) ∧
      (∀ b e, V b e ⊆ U b e) ∧
      (∀ w, MeasurableSet (H' w) ∧ H' w ⊆ H w) ∧
      (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w \ H' w)) ≤ (M : ENNReal) * θ ∧
      (∀ b, p.lev b = i → ∀ e, (V b e).Nonempty →
        θ * (ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)) ≤
          ((ν (p.γ b)).prod volume) (U b e)) ∧
      ∀ w q, q ∈ H' w → ∃ b e, p.lev b = i ∧ p.γ b = w ∧ q ∈ V b e := by
  classical
  let μ : Fin p.C → Measure Event := fun b =>
    if p.lev b = i then ((ν (p.γ b)).prod volume).restrict (H (p.γ b) ∩ p.F b) else 0
  let weight : Fin p.C → ENNReal := fun b =>
    if p.lev b = i then ENNReal.ofReal (ω (p.γ b)) else 0
  let reference : Fin p.C → ENNReal := fun b =>
    ENNReal.ofReal (((2 : ℝ) ^ p.T i)⁻¹) * ν (p.γ b) (p.A b)
  have hbudget : ∑ b, weight b * reference b ≤ 1 :=
    hp.full_reference_mass_le_one hν hω hsum i
  have hcovered (b : Fin p.C) : μ b (⋃ e, U b e)ᶜ = 0 := by
    by_cases hb : p.lev b = i
    · dsimp only [μ]
      rw [ite_eq_left hb, Measure.restrict_apply (MeasurableSet.iUnion (hU b)).compl]
      have hempty : (⋃ e, U b e)ᶜ ∩ (H (p.γ b) ∩ p.F b) = ∅ := by
        exact disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right (hcover b hb))
      rw [hempty, measure_empty]
    · simp only [μ, ite_eq_right hb, Measure.coe_zero, Pi.zero_apply]
  obtain ⟨V, hVm, hVd, hVU, hfloor, hloss⟩ :=
    heavy_original_entry_partition μ weight reference hbudget M U hU hcovered θ
  let H' : Fin W → Set Event := fun w =>
    ⋃ b : Fin p.C, if p.lev b = i ∧ p.γ b = w then ⋃ e, V b e else ∅
  have hH'm (w : Fin W) : MeasurableSet (H' w) := by
    apply MeasurableSet.iUnion
    intro b
    split_ifs
    · exact MeasurableSet.iUnion (hVm b)
    · exact MeasurableSet.empty
  have hH' (w : Fin W) (q : Event) :
      q ∈ H' w ↔ ∃ b e, p.lev b = i ∧ p.γ b = w ∧ q ∈ V b e := by
    change (q ∈ ⋃ b : Fin p.C, if p.lev b = i ∧ p.γ b = w then ⋃ e, V b e else ∅) ↔ _
    constructor
    · intro hq
      obtain ⟨b, hb⟩ := mem_iUnion.mp hq
      split_ifs at hb with hbi
      · obtain ⟨e, he⟩ := mem_iUnion.mp hb
        exact ⟨b, e, hbi.1, hbi.2, he⟩
      · exact hb.elim
    · rintro ⟨b, e, hbi, hbw, he⟩
      exact mem_iUnion.mpr ⟨b, by
        rw [ite_eq_left ⟨hbi, hbw⟩]
        exact mem_iUnion.mpr ⟨e, he⟩⟩
  have hH'sub (w : Fin W) : H' w ⊆ H w := by
    intro q hq
    obtain ⟨b, e, _, hbw, hq⟩ := (hH' w q).mp hq
    simpa only [hbw] using (hsub b e (hVU b e hq)).1
  have hglobal : (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w \ H' w)) ≤
      ∑ b, weight b * μ b (⋃ e, V b e)ᶜ := by
    let F : Fin p.C → Set Event := fun b => if p.lev b = i then p.F b else ∅
    have hcov (w : Fin W) : H w \ H' w ⊆ {q | ∃ b, p.γ b = w ∧ q ∈ F b} := by
      intro q hq
      obtain ⟨b, hbi, hbw, hqb⟩ := hp.covered_at_level H i hi hterminal w hq.1
      exact ⟨b, hbw, by simpa only [F, ite_eq_left hbi] using hqb⟩
    apply (weighted_cover_mass_le (fun w => (ν w).prod volume)
      (fun w => ENNReal.ofReal (ω w)) p.γ F (fun w => H w \ H' w) hcov).trans
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : p.lev b = i
    · simp only [weight, μ, F, ite_eq_left hb]
      apply mul_le_mul_of_nonneg_left _ zero_le
      rw [Measure.restrict_apply (MeasurableSet.iUnion (hVm b)).compl]
      apply measure_mono
      intro q hq
      refine ⟨?_, hq.1.1, hq.2⟩
      intro hqV
      obtain ⟨e, he⟩ := mem_iUnion.mp hqV
      exact hq.1.2 ((hH' (p.γ b) q).mpr ⟨b, e, hb, rfl, he⟩)
    · simp only [weight, F, ite_eq_right hb, inter_empty, measure_empty, mul_zero, zero_mul]
      exact zero_le
  refine ⟨V, H', hVm, hVd, hVU, fun w => ⟨hH'm w, hH'sub w⟩,
    hglobal.trans hloss, ?_, fun w q => (hH' w q).mp⟩
  intro b hb e he
  have hh : θ * reference b ≤
      (((ν (p.γ b)).prod volume).restrict (H (p.γ b) ∩ p.F b)) (U b e) := by
    simpa only [μ, ite_eq_left hb] using hfloor b e he
  rw [Measure.restrict_apply (hU b e), inter_eq_left.mpr (hsub b e)] at hh
  exact hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
