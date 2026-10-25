-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.EntryCompletion, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/EntryCompletion.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/EntryCompletion.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/EntryCompletion.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/EntryCompletion.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_stable_native_signal_oscillation.Partition

/-!
# Original entry floors survive later common-graph selection

Light entries are removed before any common graph is selected. One later
fitting witness then puts the entire earlier heavy entry in a slightly
wider tube, preserving its floor under the unchanged original law.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Use the accepted original-candidate pruning lemma separately on each
packet. The weighted deletion pays the original reference budget once,
independently of any later selected graph or selected mass. -/
theorem heavy_original_entry_partition
    {β X : Type*} [Fintype β] [MeasurableSpace X]
    (μ : β → Measure X) (weight reference : β → ENNReal)
    (hbudget : ∑ b, weight b * reference b ≤ 1)
    (M : ℕ) (U : β → Fin M → Set X) (hU : ∀ b e, MeasurableSet (U b e))
    (hcover : ∀ b, μ b (⋃ e, U b e)ᶜ = 0) (θ : ENNReal) :
    ∃ E : β → Fin M → Set X,
      (∀ b e, MeasurableSet (E b e)) ∧
      (∀ b, Pairwise fun e e' => Disjoint (E b e) (E b e')) ∧
      (∀ b e, E b e ⊆ U b e) ∧
      (∀ b e, (E b e).Nonempty → θ * reference b ≤ μ b (U b e)) ∧
      (∑ b, weight b * μ b (⋃ e, E b e)ᶜ) ≤ (M : ENNReal) * θ := by
  choose E hEm hEd hsub hfloor hmass using fun b =>
    k4_stable_native_signal_oscillation.retain_heavy_cover (μ b) (U b) (hU b)
      (θ * reference b) 0 (by rw [hcover b])
  refine ⟨E, hEm, hEd, hsub, hfloor, ?_⟩
  calc
    _ ≤ ∑ b, weight b * ((M : ENNReal) * (θ * reference b)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (by simpa only [zero_add] using hmass b) zero_le
    _ = ((M : ENNReal) * θ) * ∑ b, weight b * reference b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ((M : ENNReal) * θ) * 1 := mul_le_mul_of_nonneg_left hbudget zero_le
    _ = _ := mul_one _

/-- One fitting point extends to the whole earlier entry when both the
native signal oscillation and the physical base diameter are controlled.
The common graph is chosen after the entry and its bounds. -/
theorem entry_subset_tube_of_one_witness
    {X Y : Type*} [SeminormedAddCommGroup Y]
    (base : X → Y) (signal : X → ℝ) (graph : Y → ℝ) (U : Set X)
    {ε signalOsc baseDiam lip : ℝ}
    (hsignal : ∀ x ∈ U, ∀ y ∈ U, |signal x - signal y| ≤ signalOsc)
    (hbase : ∀ x ∈ U, ∀ y ∈ U, ‖base x - base y‖ ≤ baseDiam)
    (hgraph : ∀ x ∈ U, ∀ y ∈ U,
      |graph (base x) - graph (base y)| ≤ lip * ‖base x - base y‖)
    (hlip : 0 ≤ lip)
    (hwitness : ∃ x ∈ U, |signal x - graph (base x)| ≤ ε) :
    U ⊆ {x | |signal x - graph (base x)| ≤ ε + signalOsc + lip * baseDiam} := by
  obtain ⟨x₀, hx₀, hfit⟩ := hwitness
  intro x hx
  have heq : signal x - graph (base x) = (signal x - signal x₀) +
      (signal x₀ - graph (base x₀)) + (graph (base x₀) - graph (base x)) := by ring
  rw [mem_ofPred_eq, heq]
  calc
    _ ≤ |signal x - signal x₀| + |signal x₀ - graph (base x₀)| +
        |graph (base x₀) - graph (base x)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ signalOsc + ε + lip * baseDiam := by
      gcongr
      · exact hsignal x hx x₀ hx₀
      · exact (hgraph x₀ hx₀ x hx).trans
          (mul_le_mul_of_nonneg_left (hbase x₀ hx₀ x hx) hlip)
    _ = _ := by ring

/-- The entire ORIGINAL heavy-entry floor lies in the completed common
tube, with any original support and regularity conditions retained.
The floor does not depend on the mass captured by the later graph. -/
theorem original_entry_floor_in_completed_tube
    {X Y : Type*} [MeasurableSpace X] [SeminormedAddCommGroup Y]
    (μ : Measure X) (base : X → Y) (signal : X → ℝ) (graph : Y → ℝ)
    (U H : Set X) (regular : X → Prop) (floor : ENNReal)
    (hfloor : floor ≤ μ U) (hH : U ⊆ H) (hregular : ∀ x ∈ U, regular x)
    {ε signalOsc baseDiam lip : ℝ}
    (hsignal : ∀ x ∈ U, ∀ y ∈ U, |signal x - signal y| ≤ signalOsc)
    (hbase : ∀ x ∈ U, ∀ y ∈ U, ‖base x - base y‖ ≤ baseDiam)
    (hgraph : ∀ x ∈ U, ∀ y ∈ U,
      |graph (base x) - graph (base y)| ≤ lip * ‖base x - base y‖)
    (hlip : 0 ≤ lip)
    (hwitness : ∃ x ∈ U, |signal x - graph (base x)| ≤ ε) :
    floor ≤ μ {x | x ∈ H ∧ regular x ∧
      |signal x - graph (base x)| ≤ ε + signalOsc + lip * baseDiam} := by
  have hsub := entry_subset_tube_of_one_witness base signal graph U
    hsignal hbase hgraph hlip hwitness
  exact hfloor.trans (measure_mono fun x hx => ⟨hH hx, hregular x hx, hsub hx⟩)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
