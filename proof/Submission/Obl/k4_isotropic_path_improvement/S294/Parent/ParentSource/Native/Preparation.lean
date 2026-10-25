-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.Preparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/Preparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/Preparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/Preparation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/Preparation.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Path
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-!
# Deleting finitely many exceptional sets from an original residual

Power-small exceptional masses are negligible uniformly for all supplied path
factors below a sufficiently small fixed power. Deletions use original measures.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- A fixed finite list of power-small exceptions has power-small total mass. -/
theorem powerSmall_finset_sum {ι : Type*} {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (s : Finset ι) (bad : ι → ℕ → ENNReal)
    (hbad : ∀ i ∈ s, IsPowerSmall N (bad i)) :
    IsPowerSmall N (fun k => ∑ i ∈ s, bad i k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, by norm_num, Eventually.of_forall fun _ => by simp⟩
  | @insert i s hi ih =>
    have hfirst := hbad i (Finset.mem_insert_self i s)
    have hrest := ih (fun j hj => hbad j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using IsPowerSmall.add hN hfirst hrest

/-- The cutoff exponent is chosen before the path and controls every path
factor bounded by that exponent. -/
theorem powerSmall_uniform_path_budget {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {bad : ℕ → ENNReal} (hbad : IsPowerSmall N bad) (D : ℝ) (hD : 0 < D) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ κ : ℝ,
      1 ≤ κ → κ ≤ N k ^ σ → bad k ≤ ENNReal.ofReal (κ⁻¹ / D) := by
  obtain ⟨c, hc, hbad⟩ := hbad
  refine ⟨c / 2, by positivity, ?_⟩
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show -c < -(c / 2) by linarith) D
  filter_upwards [hbad, hsmall, hN.eventually (eventually_gt_atTop (0 : ℝ))]
    with k hk hsmall hNk
  intro κ hκ hκN
  have hκpos : 0 < κ := by linarith
  have hinv : N k ^ (-(c / 2)) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hNk.le]
    simpa only [one_div] using one_div_le_one_div_of_le hκpos hκN
  apply hk.trans
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hsmall.le.trans hinv)

/-- Removing at most half of a guaranteed mass preserves the other half,
without any normalization or measurability assumption on the residual. -/
theorem mixture_remove_half {Γ X : Type*} [Fintype Γ] [MeasurableSpace X]
    (μ : Γ → Measure X) (weight : Γ → ENNReal) (H bad : Γ → Set X)
    {a : ℝ} (ha : 0 ≤ a)
    (hH : ENNReal.ofReal a ≤ ∑ w, weight w * μ w (H w))
    (hbad : (∑ w, weight w * μ w (bad w)) ≤ ENNReal.ofReal (a / 2)) :
    ENNReal.ofReal (a / 2) ≤ ∑ w, weight w * μ w (H w \ bad w) := by
  have hcover (w : Γ) : H w ⊆ (H w \ bad w) ∪ bad w := by
    intro p hp
    by_cases hb : p ∈ bad w
    · exact Or.inr hb
    · exact Or.inl ⟨hp, hb⟩
  have hbound : ENNReal.ofReal a ≤
      (∑ w, weight w * μ w (H w \ bad w)) + ENNReal.ofReal (a / 2) := by
    calc
      _ ≤ ∑ w, weight w * μ w (H w) := hH
      _ ≤ ∑ w, weight w * (μ w (H w \ bad w) + μ w (bad w)) := by
        apply Finset.sum_le_sum
        intro w _
        exact mul_le_mul_of_nonneg_left
          ((measure_mono (hcover w)).trans (measure_union_le _ _)) zero_le
      _ = (∑ w, weight w * μ w (H w \ bad w)) + ∑ w, weight w * μ w (bad w) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hbad
  have hsplit : ENNReal.ofReal a = ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [hsplit] at hbound
  exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hbound

/-- Union bounds apply to the weighted original laws even when the number of
worlds varies. -/
theorem finite_exception_mixture_bound {ι Γ X : Type*} [Fintype ι] [Fintype Γ]
    [MeasurableSpace X] (μ : Γ → Measure X) (weight : Γ → ENNReal)
    (bad : ι → Γ → Set X) :
    (∑ w, weight w * μ w (⋃ i, bad i w)) ≤ ∑ i, ∑ w, weight w * μ w (bad i w) := by
  calc
    _ ≤ ∑ w, weight w * ∑ i, μ w (bad i w) := by
      exact Finset.sum_le_sum fun w _ =>
        mul_le_mul_of_nonneg_left (measure_iUnion_fintype_le _ _) zero_le
    _ = _ := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

/-- All fixed pure and angular exceptions may be deleted before choosing a
particular supplied path. The surviving mass is still measured in the original
world mixture. -/
theorem finite_exception_cleanup {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) (W : ℕ → ℕ)
    (μ : (k : ℕ) → Fin (W k) → Measure X)
    (weight : (k : ℕ) → Fin (W k) → ENNReal)
    (bad : ι → (k : ℕ) → Fin (W k) → Set X)
    (hbad : ∀ i, IsPowerSmall N (fun k => ∑ w, weight k w * μ k w (bad i k w))) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ κ : ℝ,
      1 ≤ κ → κ ≤ N k ^ σ → ∀ H : Fin (W k) → Set X,
      ENNReal.ofReal (κ⁻¹ / 2) ≤ ∑ w, weight k w * μ k w (H w) →
      ENNReal.ofReal (κ⁻¹ / 4) ≤ ∑ w, weight k w * μ k w (H w \ ⋃ i, bad i k w) := by
  have htotal := powerSmall_finset_sum hN Finset.univ
    (fun i k => ∑ w, weight k w * μ k w (bad i k w)) (fun i _ => hbad i)
  obtain ⟨σ, hσ, hbudget⟩ := powerSmall_uniform_path_budget hN htotal 4 (by norm_num)
  refine ⟨σ, hσ, hbudget.mono ?_⟩
  intro k hk κ hκ hκN H hH
  have hmass : (∑ w, weight k w * μ k w (⋃ i, bad i k w)) ≤
      ENNReal.ofReal (κ⁻¹ / 4) :=
    (finite_exception_mixture_bound (μ k) (weight k) (fun i w => bad i k w)).trans
      (hk κ hκ hκN)
  have hkeep := mixture_remove_half (μ k) (weight k) H (fun w => ⋃ i, bad i k w)
    (a := κ⁻¹ / 2) (by positivity) hH (by
      convert hmass using 1
      congr 1
      ring)
  convert hkeep using 1
  congr 1
  ring

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
