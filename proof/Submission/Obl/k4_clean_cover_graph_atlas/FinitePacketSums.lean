import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_clean_cover_graph_atlas
open Finset

/-- Removing zero-weight entries from a heavy-entry filter preserves its exact
original weighted mass. -/
theorem positive_heavy_sum_eq {α Γ : Type*} [Fintype α]
    (packet : α → Γ) (mass : α → ENNReal) (scale : Γ → ENNReal) (weight : Γ → ℝ)
    (threshold : ENNReal) (hw : ∀ g, 0 ≤ weight g) :
    (∑ a ∈ univ.filter (fun a => scale (packet a) * threshold ≤ mass a),
      ENNReal.ofReal (weight (packet a)) * mass a) =
    ∑ a ∈ univ.filter (fun a => 0 < weight (packet a) ∧ scale (packet a) * threshold ≤ mass a),
      ENNReal.ofReal (weight (packet a)) * mass a := by
  classical
  simp only [sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases h : 0 < weight (packet a)
  · simp only [h, true_and]
  · have hzero : weight (packet a) = 0 := le_antisymm (le_of_not_gt h) (hw _)
    simp [hzero]

/-- A packet-relative common-cap estimate sums against the same original
prior budget; no count of the number of old packets is spent. -/
theorem packet_constant_sum_le {α Γ : Type*} [Fintype α] [Fintype Γ] [DecidableEq Γ]
    (packet : α → Γ) (weight cap scale : Γ → ENNReal) (K : ENNReal)
    (hcap : ∀ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) * cap g ≤ K * scale g)
    (hbudget : (∑ g, weight g * scale g) ≤ 1) :
    (∑ a, weight (packet a) * cap (packet a)) ≤ K := by
  classical
  calc
    _ = ∑ g, ((univ.filter (fun a => packet a = g)).card : ENNReal) * (weight g * cap g) := by
      rw [← sum_fiberwise (univ : Finset α) packet]
      apply sum_congr rfl
      intro g _
      calc
        _ = ∑ a ∈ univ.filter (fun a => packet a = g), weight g * cap g := by
          apply sum_congr rfl
          intro a ha
          rw [(mem_filter.mp ha).2]
        _ = _ := by simp
    _ = ∑ g, weight g * (((univ.filter (fun a => packet a = g)).card : ENNReal) * cap g) := by
      apply sum_congr rfl
      intro g _
      ring
    _ ≤ ∑ g, weight g * (K * scale g) := sum_le_sum fun g _ => mul_le_mul' le_rfl (hcap g)
    _ = K * ∑ g, weight g * scale g := by
      rw [mul_sum]
      apply sum_congr rfl
      intro g _
      ring
    _ ≤ K * 1 := mul_le_mul' le_rfl hbudget
    _ = K := mul_one _

end Submission.Obl.k4_clean_cover_graph_atlas
