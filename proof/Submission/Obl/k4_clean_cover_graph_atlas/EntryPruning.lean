-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/EntryPruning.lean (namespace renamed).

import Mathlib

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Finset

/-- Packet-relative light entries are charged against the original packet mass budget.
The number of packets does not enter the bound. -/
theorem weighted_light_entry_mass_le {α Γ : Type*} [Fintype α] [Fintype Γ] [DecidableEq Γ]
    (packet : α → Γ) (mass : α → ENNReal) (scale weight : Γ → ENNReal)
    (count threshold : ENNReal)
    (hcount : ∀ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) ≤ count) :
    (∑ a ∈ univ.filter (fun a => mass a < scale (packet a) * threshold),
      weight (packet a) * mass a) ≤
      count * threshold * ∑ g, weight g * scale g := by
  classical
  let light : α → ENNReal := fun a =>
    if mass a < scale (packet a) * threshold then weight (packet a) * mass a else 0
  have hpoint (a : α) : light a ≤ weight (packet a) * scale (packet a) * threshold := by
    dsimp only [light]
    split_ifs with ha
    · simpa only [mul_assoc] using mul_le_mul' le_rfl ha.le
    · exact zero_le
  calc
    _ = ∑ a, light a := by simp only [light, sum_filter]
    _ ≤ ∑ a, weight (packet a) * scale (packet a) * threshold :=
      sum_le_sum fun a _ => hpoint a
    _ = ∑ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) *
        (weight g * scale g * threshold) := by
      rw [← sum_fiberwise (univ : Finset α) packet]
      apply sum_congr rfl
      intro g _
      calc
        _ = ∑ a ∈ univ.filter (fun a => packet a = g),
            weight g * scale g * threshold := by
          apply sum_congr rfl
          intro a ha
          rw [(mem_filter.mp ha).2]
        _ = _ := by simp
    _ ≤ ∑ g, count * (weight g * scale g * threshold) :=
      sum_le_sum fun g _ => mul_le_mul' (hcount g) le_rfl
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro g _
      ring

/-- Keeping all entries above a packet-relative threshold loses only the light-entry
budget, even when the original packet masses are unequal. -/
theorem weighted_heavy_entry_floor {α Γ : Type*} [Fintype α] [Fintype Γ] [DecidableEq Γ]
    (packet : α → Γ) (mass : α → ENNReal) (scale weight : Γ → ENNReal)
    (count threshold : ENNReal)
    (hcount : ∀ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) ≤ count) :
    (∑ a, weight (packet a) * mass a) ≤
      (∑ a ∈ univ.filter (fun a => scale (packet a) * threshold ≤ mass a),
        weight (packet a) * mass a) +
      count * threshold * ∑ g, weight g * scale g := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (s := (univ : Finset α))
    (p := fun a => scale (packet a) * threshold ≤ mass a)
    (f := fun a => weight (packet a) * mass a)
  simp only [not_le] at hsplit
  rw [← hsplit]
  exact add_le_add le_rfl
    (weighted_light_entry_mass_le packet mass scale weight count threshold hcount)

/-- A normalized original packet budget turns the pruning loss into a single scalar. -/
theorem weighted_light_entry_mass_le_of_budget {α Γ : Type*} [Fintype α] [Fintype Γ] [DecidableEq Γ]
    (packet : α → Γ) (mass : α → ENNReal) (scale weight : Γ → ENNReal)
    (count threshold : ENNReal)
    (hcount : ∀ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) ≤ count)
    (hbudget : (∑ g, weight g * scale g) ≤ 1) :
    (∑ a ∈ univ.filter (fun a => mass a < scale (packet a) * threshold),
      weight (packet a) * mass a) ≤ count * threshold := by
  exact (weighted_light_entry_mass_le packet mass scale weight count threshold hcount).trans
    (by simpa only [mul_one] using mul_le_mul' le_rfl hbudget)

/-- The candidate-count exponent cancels against its packet-relative light threshold. -/
theorem entry_pruning_power_cancellation {N base slack penalty : ℝ} (hN : 0 < N) :
    ENNReal.ofReal (N ^ (base + slack)) * ENNReal.ofReal (N ^ (-base - penalty)) =
      ENNReal.ofReal (N ^ (slack - penalty)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _), ← Real.rpow_add hN]
  congr 2
  ring

end Submission.Obl.k4_clean_cover_graph_atlas
