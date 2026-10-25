import Submission.Obl.k4_unbounded_geometric_packet_reduction.PacketBudgets
import Submission.Obl.k4_unbounded_geometric_packet_reduction.RecoveryNumerics

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

/-- Removing light conditional laws uses the original fixed total budget.
The retained subtype is ready for a finite atlas enumeration. -/
theorem retained_heavy_mass {I : Type*} [Fintype I]
    (R m : I → ENNReal) (hR : ∑ i, R i ≤ 1) {a b θ δ : ℝ}
    (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hδ : 0 ≤ δ)
    (hgap : 2 * b + θ + δ ≤ a)
    (hmass : ENNReal.ofReal a ≤ (∑ i, R i * m i) + ENNReal.ofReal δ) :
    ENNReal.ofReal b ≤ ∑ i : {i : I | ENNReal.ofReal θ ≤ m i}, R i.val * m i.val := by
  classical
  let recovered (i : I) : ENNReal := if ENNReal.ofReal θ ≤ m i then m i else 0
  have hrec i (hi : ENNReal.ofReal θ ≤ m i) : m i ≤ 2 * recovered i := by
    simpa only [recovered, if_pos hi] using
      (le_mul_of_one_le_left (show (0 : ENNReal) ≤ m i from zero_le)
        (by norm_num : (1 : ENNReal) ≤ 2))
  have hs : (∑ i, R i * recovered i) =
      ∑ i : {i : I | ENNReal.ofReal θ ≤ m i}, R i.val * m i.val := by
    simp only [recovered, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hh := packet_recovery_mass R m recovered (ENNReal.ofReal θ) hR hrec
  rw [hs] at hh
  apply recovery_mass_lower hb (add_nonneg hθ hδ) (by linarith)
  calc
    ENNReal.ofReal a ≤ (∑ i, R i * m i) + ENNReal.ofReal δ := hmass
    _ ≤ (2 * ∑ i : {i : I | ENNReal.ofReal θ ≤ m i}, R i.val * m i.val +
        ENNReal.ofReal θ) + ENNReal.ofReal δ := add_le_add hh le_rfl
    _ = _ := by rw [ENNReal.ofReal_add hθ hδ]; ac_rfl

end Submission.Obl.k4_unbounded_geometric_packet_reduction
