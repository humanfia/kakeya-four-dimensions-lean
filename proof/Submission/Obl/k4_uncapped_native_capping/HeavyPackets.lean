/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/MassBookkeeping.lean (only the three
light/heavy packet mass lemmas; namespace renamed to Submission.Obl.k4_uncapped_native_capping).
Existing source attributions below are retained.
-/
import Mathlib

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
noncomputable section

/- The following light-packet bound is adapted from this LOT tree o178,
   x0639, `PacketBudgets.lean`, commit 584004b954271834a15b62ddaea1097c68953739. -/
theorem light_packet_mass_le {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) (θ : ENNReal) (hw : ∑ i, w i ≤ 1) :
    (∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * m i) ≤ θ := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * θ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul' le_rfl (Finset.mem_filter.mp hi).2.le
    _ = θ * ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ ≤ θ * ∑ i, w i := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => bot_le)
    _ ≤ θ * 1 := mul_le_mul' le_rfl hw
    _ = θ := mul_one _

theorem mass_le_heavy_add_threshold {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) (θ : ENNReal) (hw : ∑ i, w i ≤ 1) :
    (∑ i, w i * m i) ≤
      (∑ i ∈ Finset.univ.filter (fun i => θ ≤ m i), w i * m i) + θ := by
  classical
  calc
    _ = (∑ i ∈ Finset.univ.filter (fun i => θ ≤ m i), w i * m i) +
        ∑ i ∈ Finset.univ.filter (fun i => m i < θ), w i * m i := by
      simpa only [not_le] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ ≤ m i)
          (fun i => w i * m i)).symm
    _ ≤ _ := add_le_add le_rfl (light_packet_mass_le w m θ hw)

theorem heavy_packet_mass_lower {ι : Type*} [Fintype ι]
    (w m : ι → ENNReal) {b θ : ENNReal} (hθ : θ ≠ ⊤)
    (hw : ∑ i, w i ≤ 1) (hmass : b + θ ≤ ∑ i, w i * m i) :
    b ≤ ∑ i ∈ Finset.univ.filter (fun i => θ ≤ m i), w i * m i := by
  classical
  exact ENNReal.le_of_add_le_add_right hθ
    (hmass.trans (mass_le_heavy_add_threshold w m θ hw))

end
end Submission.Obl.k4_uncapped_native_capping
