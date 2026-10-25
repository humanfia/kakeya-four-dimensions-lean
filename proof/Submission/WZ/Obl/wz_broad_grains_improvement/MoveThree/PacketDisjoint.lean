-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PacketDisjoint.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PacketDisjoint.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainRefinement

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (assignedFiber bodyCount body_mass_le_mul_of_count)
open WangZahlLot.Obl.wz_measurable_angular_selection (measurableSet_pattern)

noncomputable section

local instance packetDisjointDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Select one active packet at each point. A bound on the number of active
packets, independent of the total number of packets, controls the mass loss. -/
theorem disjoint_packet_refinement {n K : ℕ} (hK : 0 < K) {B : ℝ} (hB : 0 < B)
    (f : Fin n → Fin K) (Y : Fin n → Set V) (hY : ∀ i, MeasurableSet (Y i))
    (hactive : ∀ p, (((Finset.univ.filter fun i => p ∈ Y i).image f).card : ℝ) ≤ B) :
    ∃ Z : Fin n → Set V,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      O (B⁻¹) * ∑ i, μ (Y i) ≤ ∑ i, μ (Z i) ∧
      (∀ p, bodyCount Y p ≤ B * bodyCount Z p) ∧
      ∀ k l, k ≠ l → Disjoint (assignedFiber f Z k) (assignedFiber f Z l) := by
  classical
  let : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hex (S : Finset (Fin n)) : ∃ k : Fin K, ∀ l : Fin K,
      (S.filter fun i => f i = l).card ≤ (S.filter fun i => f i = k).card := by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
      (fun k => (S.filter fun i => f i = k).card) Finset.univ_nonempty
    exact ⟨k, fun l => hk l (Finset.mem_univ _)⟩
  choose a ha using hex
  have hbound (S : Finset (Fin n)) :
      S.card ≤ (S.image f).card * (S.filter fun i => f i = a S).card := by
    calc
      _ = ∑ k ∈ S.image f, (S.filter fun i => f i = k).card := Finset.card_eq_sum_card_image f S
      _ ≤ ∑ _k ∈ S.image f, (S.filter fun i => f i = a S).card :=
        Finset.sum_le_sum (fun k _ => ha S k)
      _ = _ := by simp
  let pattern := fun p => Finset.univ.filter fun i => p ∈ Y i
  have hpat (p : V) (i : Fin n) : i ∈ pattern p ↔ p ∈ Y i := by simp [pattern]
  let Z := fun i => {p | p ∈ Y i ∧ f i = a (pattern p)}
  have hZm (i : Fin n) : MeasurableSet (Z i) := by
    have hm := measurableSet_pattern hY pattern hpat (fun S => i ∈ S ∧ f i = a S)
    simpa only [hpat] using hm
  have hYcount (p : V) : bodyCount Y p = ((pattern p).card : ℝ) := by
    simp [bodyCount, pattern, Set.ncard_eq_toFinset_card']
  have hZcount (p : V) : bodyCount Z p =
      (((pattern p).filter fun i => f i = a (pattern p)).card : ℝ) := by
    have he : {i | p ∈ Z i} =
        ((pattern p).filter fun i => f i = a (pattern p) : Set (Fin n)) := by
      ext i
      simp [Z, hpat]
    simp only [bodyCount, he, Set.ncard_coe_finset]
  have hpoint (p : V) : bodyCount Y p ≤ B * bodyCount Z p := by
    have hactive' : (((pattern p).image f).card : ℝ) ≤ B := by
      exact hactive p
    rw [hYcount, hZcount]
    calc
      _ ≤ (((pattern p).image f).card : ℝ) *
          (((pattern p).filter fun i => f i = a (pattern p)).card : ℝ) := by
        exact_mod_cast hbound (pattern p)
      _ ≤ _ := mul_le_mul_of_nonneg_right hactive' (Nat.cast_nonneg _)
  have hmass := body_mass_le_mul_of_count hY hZm hB.le hpoint
  refine ⟨Z, fun i => ⟨hZm i, fun p hp => hp.1⟩, ?_, hpoint, ?_⟩
  · calc
      _ ≤ O (B⁻¹) * (O B * ∑ i, μ (Z i)) := mul_le_mul' le_rfl hmass
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hB.le),
          inv_mul_cancel₀ hB.ne']
        simp only [O, ENNReal.ofReal_one, one_mul]
  · intro k l hkl
    apply Set.disjoint_left.mpr
    rintro p ⟨i, hik, hi⟩ ⟨j, hjl, hj⟩
    exact hkl ((hik.symm.trans hi.2).trans (hjl.symm.trans hj.2).symm)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
