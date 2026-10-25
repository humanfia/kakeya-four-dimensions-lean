import Submission.Obl.k4_native_calibrated_homogeneous_remainder.AtlasSelection

/-! Retain complete worlds, reindex their original charts, and normalize the
weights without changing any retained prior or coefficient map. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable def RemainderGeometry.retainWorlds {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (S : (k : ℕ) → Finset (Fin (q.W k)))
    (K : ℕ → ℝ) (ht : ∀ k, 0 < keptWeightSum q S k ∧ keptWeightSum q S k ≤ 1)
    (hlower : ∀ k, (a.κ k)⁻¹ ≤ a.Z k * keptWeightSum q S k) :
    RemainderGeometry p (keepWorlds q S K) r h w := by
  classical
  refine { a with
    parent := a.retainedAtlas S
    worlds := fun k => Equiv.refl (Fin (S k).card)
    parent_valid := ?_
    width_bound := fun k b => a.width_bound k (a.retainedIndex S k b)
    θ := fun k b => a.θ k (keptWorldIndex (S k) b)
    index_preserved := fun k b => a.index_preserved k (keptWorldIndex (S k) b)
    planar_map := fun k b => a.planar_map k (keptWorldIndex (S k) b)
    hidden_map := fun k b => a.hidden_map k (keptWorldIndex (S k) b)
    prior_pos := fun k b => a.prior_pos k (keptWorldIndex (S k) b)
    prior_inverse_bound := fun k b => a.prior_inverse_bound k (keptWorldIndex (S k) b)
    conditioned_prior := fun k b => a.conditioned_prior k (keptWorldIndex (S k) b)
    selected_pullback := fun k b => a.selected_pullback k (keptWorldIndex (S k) b)
    derivative_unit := fun k b => a.derivative_unit k (keptWorldIndex (S k) b)
    Z := fun k => a.Z k * keptWeightSum q S k
    normalizer_pos := fun k => mul_pos (a.normalizer_pos k) (ht k).1
    normalizer_lower := hlower
    normalizer_upper := fun k =>
      (mul_le_mul (a.normalizer_upper k) (ht k).2 (ht k).1.le zero_le_one).trans_eq (one_mul _)
    normalizer_sum := ?_
    world_weights := ?_ }
  · intro k
    have hc : (S k).card ≤ (a.parent k).C := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective (a.retainedIndex S k) (a.retainedIndex_injective S k)
    refine ⟨(Nat.cast_le.mpr hc).trans (a.parent_valid k).1, ?_,
      fun b => (a.parent_valid k).2.2 (a.retainedIndex S k b)⟩
    intro b b' hne hγ hj
    exact (a.parent_valid k).2.1 _ _
      (fun heq => hne ((a.retainedIndex_injective S k) heq)) hγ hj
  · intro k
    change a.Z k * keptWeightSum q S k = ∑ b : Fin (S k).card,
      p.ω (a.φ k) ((a.parent k).γ (a.worlds k (keptWorldIndex (S k) b))) /
        (2 : ℝ) ^ (a.parent k).T *
        (p.ν (a.φ k) ((a.parent k).γ (a.worlds k (keptWorldIndex (S k) b)))
          ((a.parent k).A (a.worlds k (keptWorldIndex (S k) b)))).toReal
    rw [sum_keptWorldIndex (S k) (fun b =>
      p.ω (a.φ k) ((a.parent k).γ (a.worlds k b)) / (2 : ℝ) ^ (a.parent k).T *
        (p.ν (a.φ k) ((a.parent k).γ (a.worlds k b)) ((a.parent k).A (a.worlds k b))).toReal)]
    rw [keptWeightSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [a.world_weights k b]
    field_simp [(a.normalizer_pos k).ne']
  · intro k b
    change q.ω k (keptWorldIndex (S k) b) / keptWeightSum q S k =
      (p.ω (a.φ k) ((a.parent k).γ (a.worlds k (keptWorldIndex (S k) b))) /
        (2 : ℝ) ^ (a.parent k).T *
        (p.ν (a.φ k) ((a.parent k).γ (a.worlds k (keptWorldIndex (S k) b)))
          ((a.parent k).A (a.worlds k (keptWorldIndex (S k) b)))).toReal) /
        (a.Z k * keptWeightSum q S k)
    rw [a.world_weights k (keptWorldIndex (S k) b)]
    field_simp [(a.normalizer_pos k).ne', (ht k).1.ne']

noncomputable def RawRemainder.retainWorlds {p q : Data} {r h w : ℝ}
    (a : RawRemainder p q r h w) (S : (k : ℕ) → Finset (Fin (q.W k)))
    (K : ℕ → ℝ) (hvalid : RawValid (keepWorlds q S K))
    (ht : ∀ k, 0 < keptWeightSum q S k ∧ keptWeightSum q S k ≤ 1)
    (hlower : ∀ k, (a.κ k)⁻¹ ≤ a.Z k * keptWeightSum q S k) :
    RawRemainder p (keepWorlds q S K) r h w := by
  classical
  refine {
    toRemainderGeometry := a.toRemainderGeometry.retainWorlds S K ht hlower
    raw_valid := hvalid
    listed := ?_
    list_bound := ?_ }
  · intro k b z hz
    exact (subatlas_mem_list (a.parent k) (a.toRemainderGeometry.retainedIndex S k)
      ((a.parent k).γ (a.toRemainderGeometry.retainedIndex S k b))
      (obs (p.B (a.φ k) ((a.parent k).γ (a.toRemainderGeometry.retainedIndex S k b)))
        (δ (p.N (a.φ k)) p.L) z) b).mpr (a.listed k _ z hz)
  · intro k γ o
    exact (Nat.cast_le.mpr (subatlas_list_card_le (a.parent k)
      (a.toRemainderGeometry.retainedIndex S k) (a.toRemainderGeometry.retainedIndex_injective S k)
      γ o)).trans (a.list_bound k γ o)

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
