-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.FiberPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.SeparatedEmbedding
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.FrozenPackets

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, FiberPackets.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V P I q bodyCount assignedFiber coarseLinear dualLinear rotatedFrame
   boxAxis geometricPacketOverlap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd)

/-- Narrow families can be packeted in all coarse frames simultaneously.
The packets preserve coarse labels and have uniformly bounded overlap in
each original coarse fibre. -/
theorem fiber_narrow_packets {L N : ℕ} {ρ a c s : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hac : a ≤ ρ * c)
    (hc : 0 < c) (hc1 : c ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ ρ * s * c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (H : Fin L → Set V)
    (γ : Fin L → Fin N) (R : Fin N → V ≃ₗᵢ[ℝ] V)
    (hH : ∀ j, (H j).Nonempty ∧ H j ⊆ P a (ρ * c) c (z j) (e j) ∧ H j ⊆ I)
    (haxis : ∀ j, ‖coarseLinear ρ (boxAxis (rotatedFrame (R (γ j)) (e j)) 2)‖ ≤ 43)
    (hnarrow : ∀ j j' p, γ j = γ j' → p ∈ H j → p ∈ H j' → s = 1 ∨
      pd (unit (dualLinear ρ (boxAxis (rotatedFrame (R (γ j)) (e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (R (γ j')) (e j')) 0))) ≤ s) :
    ∃ K : ℕ, ∃ f : Fin L → Fin K, ∃ ref : Fin K → Fin L,
      (∀ k, f (ref k) = k) ∧
      (∀ j, γ (ref (f j)) = γ j) ∧
      (∀ j j', f j = f j' → γ j = γ j' ∧
        ‖unit (dualLinear ρ (boxAxis (rotatedFrame (R (γ j)) (e j)) 0)) -
          unit (dualLinear ρ (boxAxis (rotatedFrame (R (γ j')) (e j')) 0))‖ ≤ s / 100 ∧
        ‖coarseLinear ρ (R (γ j) (z j - z j'))‖ ≤ c / 100 ∧
        |inner ℝ (unit (dualLinear ρ (boxAxis (rotatedFrame (R (γ j')) (e j')) 0)))
          (coarseLinear ρ (R (γ j) (z j - z j')))| ≤ s * c / 100) ∧
      ∀ k p, q K {j | γ (ref j) = k ∧ p ∈ assignedFiber f H j} ≤ geometricPacketOverlap := by
  classical
  let z' (j : Fin L) := fiberEmbed R (γ j) (z j)
  let e' (j : Fin L) := rotatedFrame (R (γ j)) (e j)
  let H' (j : Fin L) := fiberEmbed R (γ j) '' H j
  have hbc : ρ * c ≤ c := by nlinarith
  have hz (j : Fin L) : ‖z j‖ ≤ 2 := by
    obtain ⟨p, hp⟩ := (hH j).1
    have hpz := WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_norm
      ha.le hac hbc (z j) (e j) ((hH j).2.1 hp)
    have hp0 : ‖p‖ < 1 := by simpa only [I, mem_ball, dist_zero_right] using (hH j).2.2 hp
    have hh := norm_sub_le p (p - z j)
    rw [sub_sub_cancel] at hh
    linarith
  have hsource (j : Fin L) : H' j ⊆ P a (ρ * c) c (z' j) (e' j) := by
    rintro _ ⟨p, hp, rfl⟩
    exact (fiberEmbed_mem_prism R (γ j) (e j) a (ρ * c) c (z j) p).mpr ((hH j).2.1 hp)
  have hnarrow' (j j' : Fin L) (p : V) (hp : p ∈ H' j) (hp' : p ∈ H' j') :
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (e' j) 0)))
        (unit (dualLinear ρ (boxAxis (e' j') 0))) ≤ s := by
    obtain ⟨u, hu, hpu⟩ := hp
    obtain ⟨v, hv, hpv⟩ := hp'
    have hu0 : ‖u‖ ≤ 2 := by
      have hh : ‖u‖ < 1 := by simpa only [I, mem_ball, dist_zero_right] using (hH j).2.2 hu
      linarith
    have hv0 : ‖v‖ ≤ 2 := by
      have hh : ‖v‖ < 1 := by simpa only [I, mem_ball, dist_zero_right] using (hH j').2.2 hv
      linarith
    have hγ : γ j = γ j' := fiberEmbed_label_eq R hu0 hv0 (by rw [hpu, hpv, sub_self, norm_zero]; norm_num)
    have huv : u = v := fiberEmbed_injective R (γ j) (by simpa only [← hγ] using hpu.trans hpv.symm)
    subst v
    exact hnarrow j j' u hγ hu hv
  obtain ⟨K, f, ref, href, hclose, hcount⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_narrow_packets hρ hρ1 hρ le_rfl
      ha hac hc hs hs1 has z' e' H' haxis hsource hnarrow'
  have hγpair (j j' : Fin L) (he : f j = f j') : γ j = γ j' := by
    have hh := (hclose j j' he).2.2.1
    have hnorm := WangZahlLot.Obl.wz_clustered_cover_volume_gain.norm_le_coarseLinear hρ hρ1 (z' j - z' j')
    exact fiberEmbed_label_eq R (hz j) (hz j') (hnorm.trans (hh.trans (by linarith)))
  have hγref (j : Fin L) : γ (ref (f j)) = γ j := hγpair _ _ (href _)
  refine ⟨K, f, ref, href, hγref, ?_, ?_⟩
  · intro j j' he
    obtain ⟨hn, _, hzclose, hsclose⟩ := hclose j j' he
    have hγ := hγpair j j' he
    have hdiff : z' j - z' j' = R (γ j) (z j - z j') := by
      dsimp only [z']
      rw [← hγ, fiberEmbed_sub]
    rw [hdiff] at hzclose hsclose
    exact ⟨hγ, hn, hzclose, hsclose⟩
  · intro k p
    apply le_trans _ (hcount (fiberEmbed R k p))
    apply Nat.cast_le.mpr
    apply Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro l hl
    obtain ⟨hγl, j, hj, hp⟩ := hl
    have hγj : γ j = k := by rw [← hγref j, hj]; exact hγl
    exact ⟨j, hj, p, hp, by rw [hγj]⟩

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
