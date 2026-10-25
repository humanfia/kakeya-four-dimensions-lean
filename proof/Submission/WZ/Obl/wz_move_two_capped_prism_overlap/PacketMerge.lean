-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.PacketMerge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.FiberPackets
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PacketCrossing
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.RotationCrossing
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.MergeScale
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.CoarseEnlarge

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, PacketMerge.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V O I P T X q ι bodyCount assignedFiber coarseLinear dualLinear rotatedFrame
   boxAxis geometricPacketOverlap)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd)

set_option maxHeartbeats 1500000 in
/-- Narrow prism shadings merge into a family with uniformly bounded
same-coarse-tube overlap. This construction keeps all fine incidence mass. -/
theorem merge_narrow_prisms {ω ζ δ h h' ρ c s : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (hh : 0 ≤ h)
    (hβ : 0 ≤ ω * ζ / 100) (hρsmall : ρ ≤ 1 / 16384)
    (hcsmall : c ≤ 1 / 1048576) (hδc : 4 * δ ≤ c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ ρ * s * c)
    (hbudget : 8796093022208 * δ ^ h' * ρ * s * c ≤ δ ^ h * D.a)
    (hangular : δ ^ (-h) * (16384 : ℝ) ^ (ω * ζ / 100) ≤ δ ^ (-h'))
    (hv : ∀ i, ‖v i‖ = 1) (hYI : ∀ i, Y i ⊆ I) (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (H : D.Valid ω ζ δ h ρ c x v Y 1)
    (hX : X (16384 * ρ) D.N D.y D.w)
    (R : Fin D.N → V ≃ₗᵢ[ℝ] V)
    (hR : ∀ k, |R k (D.w k) 0| ≤ ρ ∧ |R k (D.w k) 1| ≤ ρ)
    (hclear : ∀ i j, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ * c) c (D.z j) (D.e j),
      96 * c < dist p (x i) ∧ 96 * c < dist p (x i + v i))
    (hnarrow : ∀ j j' p, D.γ j = D.γ j' → p ∈ ⋃ i, D.W i j → p ∈ ⋃ i, D.W i j' →
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j')) (D.e j')) 0))) ≤ s) :
    ∃ D' : PrismData n,
      D'.Valid ω ζ δ h' (16384 * ρ) (32 * c) x v Y 1 ∧
      (∀ k p, q D'.L {j | D'.γ j = k ∧ p ∈ ⋃ i, D'.W i j} ≤ geometricPacketOverlap) ∧
      (∑ i, ∑ j, volume (D'.W i j)) = ∑ i, ∑ j, volume (D.W i j) := by
  classical
  have Hcopy := H
  rcases Hcopy with ⟨ha, hab, hbc, hc1, hW, _, _, hcross, _, _, hw, hcover, _⟩
  have ha0 := hδ.trans_le ha
  have hc : 0 < c := ha0.trans_le (hab.trans hbc)
  have hρ : 0 < ρ := (mul_pos_iff.mp (ha0.trans_le hab)).resolve_right
    (by intro h; linarith [h.2]) |>.1
  have hρ1 : ρ ≤ 1 := by linarith
  have hρρ : ρ ≤ 16384 * ρ := by linarith
  have hsource (j : Fin D.L) : (⋃ i, D.W i j).Nonempty ∧
      (⋃ i, D.W i j) ⊆ P D.a (ρ * c) c (D.z j) (D.e j) ∧ (⋃ i, D.W i j) ⊆ I := by
    obtain ⟨i, hi⟩ := valid_prism_nonempty D hδ H j
    refine ⟨hi.mono (subset_iUnion (fun i => D.W i j) i),
      iUnion_subset (fun i => (hW i j).2.1.trans inter_subset_right),
      iUnion_subset (fun i => (hW i j).2.1.trans (inter_subset_left.trans (hYI i)))⟩
  have haxes (j : Fin D.L) :
      ‖dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)‖ ≤ 25 * ρ ∧
      ‖dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 1)‖ ≤ 25 * ρ ∧
      ‖coarseLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 2)‖ ≤ 43 := by
    apply WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_coarse_axis_bounds hρ hρ1 hρ.le le_rfl
      _ (R (D.γ j) (D.w (D.γ j)))
    · simpa only [(R (D.γ j)).norm_map] using hw (D.γ j)
    · exact (hR (D.γ j)).1
    · exact (hR (D.γ j)).2
    · simpa only [WangZahlLot.Obl.wz_clustered_cover_volume_gain.rotatedFrame_apply] using
        ((hcover (by norm_num)).2 j).2
  obtain ⟨K, f, ref, href, hγ, hpacket, hcount⟩ := fiber_narrow_packets hρ hρ1 ha0 hab hc hc1
    hs hs1 has D.z D.e (fun j => ⋃ i, D.W i j) D.γ R hsource (fun j => (haxes j).2.2) hnarrow
  let a' : ℝ := 524288 * ρ * s * c
  let b' : ℝ := 524288 * ρ * c
  let c' : ℝ := 32 * c
  have ha' : δ ≤ a' := by dsimp only [a']; nlinarith
  have hab' : a' ≤ b' := by dsimp only [a', b']; nlinarith [mul_pos hρ hc]
  have hb' : 0 < b' := by dsimp only [b']; positivity
  have hc' : 0 < c' := by dsimp only [c']; positivity
  have hbeq : (16384 * ρ) * c' = b' := by dsimp only [b', c']; ring
  have hpc (j : Fin D.L) := hpacket j (ref (f j)) (href (f j)).symm
  have hcore (j : Fin D.L) : P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P (a' / 8) (b' / 8) (c' / 8) (D.z (ref (f j))) (D.e (ref (f j))) := by
    intro p hp
    let Rj := R (D.γ j)
    have hnormal := (hpc j).2.1
    have hshort := (hpc j).2.2.2
    rw [hγ j] at hnormal hshort
    have hD0 := (haxes (ref (f j))).1
    have hD1 := (haxes (ref (f j))).2.1
    rw [hγ j] at hD0 hD1
    have hh := packet_prism_in_core (ρ := ρ) (a := D.a) (c := c) (s := s)
      (z := Rj (D.z j)) (z₀ := Rj (D.z (ref (f j)))) (rotatedFrame Rj (D.e j))
      (rotatedFrame Rj (D.e (ref (f j)))) hρ hρ1 ha0 hab hc hs has hD0 hD1
      (haxes j).2.2 (hnormal.trans (by linarith))
      (by simpa only [← map_sub] using (hpc j).2.2.1)
      (by simpa only [← map_sub] using hshort)
      ((rotated_prism_mem Rj (D.e j) D.a (ρ * c) c (D.z j) p).mpr hp)
    exact (rotated_prism_mem Rj (D.e (ref (f j))) (a' / 8) (b' / 8) (c' / 8)
      (D.z (ref (f j))) p).mp hh
  have hcontain (j : Fin D.L) : P D.a (ρ * c) c (D.z j) (D.e j) ⊆
      P a' b' c' (D.z (ref (f j))) (D.e (ref (f j))) := by
    intro p hp
    have hp' := hcore j hp
    exact ⟨hp'.1.trans (by linarith), hp'.2.1.trans (by linarith), hp'.2.2.trans (by linarith)⟩
  have hcross' (i : Fin n) (j : Fin D.L) (hi : (D.W i j).Nonempty) :
      (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a' b' c' (D.z (ref (f j))) (D.e (ref (f j)))),
        |ι (D.e (ref (f j)) (p - D.z (ref (f j)))) 2| = c' / 2) ∧
      ∀ t ∈ ({-c'/2,c'/2} : Set ℝ), ∃ p ∈ T δ (x i) (v i) ∩
        P a' b' c' (D.z (ref (f j))) (D.e (ref (f j))),
        ι (D.e (ref (f j)) (p - D.z (ref (f j)))) 2 = t := by
    let Rj := R (D.γ j)
    obtain ⟨p, hp⟩ := hi
    have hpU := ((hW i j).2.1 hp).2
    have hpT := hYT i ((hW i j).2.1 hp).1
    obtain ⟨ht, hfr, hend⟩ := hcross i j ⟨p, hp⟩
    rw [(hcover (by norm_num)).1] at ht
    have htr : T δ (Rj (x i)) (Rj (v i)) ⊆ T ρ (Rj (D.y (D.γ j))) (Rj (D.w (D.γ j))) := by
      intro q hq
      have hq' : Rj (Rj.symm q) ∈ T δ (Rj (x i)) (Rj (v i)) := by simpa only [Rj.apply_symm_apply] using hq
      have hqold := (rotated_tube_mem Rj δ (x i) (v i) _).mp hq'
      simpa only [Rj.apply_symm_apply] using (rotated_tube_mem Rj ρ (D.y (D.γ j)) (D.w (D.γ j)) _).mpr (ht hqold)
    have hvnorm : ‖Rj (v i)‖ = 1 := by simpa only [Rj.norm_map] using hv i
    have hwcoarse : ‖Rj (D.w (D.γ j))‖ = 1 := by simpa only [Rj.norm_map] using hw (D.γ j)
    have hvcoarse := contained_direction_coarse_norm hδ hρ hvnorm hwcoarse
      (hR (D.γ j)).1 (hR (D.γ j)).2 htr
    have hcrot := (rotated_prism_crossing_iff Rj (D.e j) δ D.a (ρ * c) c (x i) (v i) (D.z j)).mpr ⟨hfr, hend⟩
    have hnormal := (hpc j).2.1
    have hshort := (hpc j).2.2.2
    have hD0 := (haxes (ref (f j))).1
    have hD1 := (haxes (ref (f j))).2.1
    rw [hγ j] at hnormal hshort hD0 hD1
    have hclr := hclear i j ⟨p, hp⟩ p hpU
    apply (rotated_prism_crossing_iff Rj (D.e (ref (f j))) δ a' b' c'
      (x i) (v i) (D.z (ref (f j)))).mp
    apply packet_prism_crossing (δ := δ) (ρ := ρ) (a := D.a) (c := c) (s := s)
      (x := Rj (x i)) (v := Rj (v i)) (z := Rj (D.z j)) (z₀ := Rj (D.z (ref (f j))))
      (q := Rj p) (rotatedFrame Rj (D.e j)) (rotatedFrame Rj (D.e (ref (f j))))
      hδ ha hδc hρ hρsmall hab hs hs1 has hvnorm hvcoarse hD0 hD1 (haxes j).2.2
      (hnormal.trans (by linarith))
      (by simpa only [← map_sub] using (hpc j).2.2.1)
      (by simpa only [← map_sub] using hshort) hcrot.2
      ⟨(rotated_tube_mem Rj δ (x i) (v i) p).mpr hpT,
        (rotated_prism_mem Rj (D.e j) D.a (ρ * c) c (D.z j) p).mpr hpU⟩
    · simpa only [Rj.dist_map] using hclr.1
    · simpa only [← map_add, Rj.dist_map] using hclr.2
  let D' := D.mergeScale (16384 * ρ) f a' (D.z ∘ ref) (D.e ∘ ref) (D.γ ∘ ref)
  have hvalid : D'.Valid ω ζ δ h' (16384 * ρ) c' x v Y 1 := by
    apply valid_merge_at_scale D x v Y hδ hδ1 hhh hh hβ hρρ
      (by simpa only [mul_div_cancel_right₀ _ hρ.ne'] using hangular) hX H f
      (D.z ∘ ref) (D.e ∘ ref) (D.γ ∘ ref) hγ ha'
    · rw [hbeq]; exact hab'
    · rw [hbeq]; dsimp only [b', c']; nlinarith
    · dsimp only [c']; nlinarith
    · intro j
      rw [hbeq]
      exact hcontain j
    · intro k
      refine ⟨ref k, href k, ?_⟩
      rw [hbeq]
      change O (δ ^ h') * volume (P a' b' c' (D.z (ref k)) (D.e (ref k))) ≤
        O (δ ^ h) * volume (P D.a (ρ * c) c (D.z (ref k)) (D.e (ref k)))
      rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume (hδ.trans_le ha').le hb'.le hc'.le,
        WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha0.le (mul_pos hρ hc).le hc.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h'),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le h)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (8796093022208 * δ ^ h' * ρ * s * c) * (ρ * c ^ 2) := by dsimp only [a', b', c']; ring
        _ ≤ (δ ^ h * D.a) * (ρ * c ^ 2) := mul_le_mul_of_nonneg_right hbudget (by positivity)
        _ = _ := by ring
    · intro i j hi
      rw [hbeq]
      exact hcross' i j hi
    · intro k
      rw [hbeq]
      obtain ⟨i, hi⟩ := valid_prism_nonempty D hδ H (ref k)
      have hcs := (hcross' i (ref k) hi).2
      rw [href k] at hcs
      have ht := (hcross i (ref k) hi).1
      rw [(hcover (by norm_num)).1] at ht
      have hcv := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_subset_expanded_coarse
        (hδ.trans_le ha').le hab' hb' hc' (by dsimp only [b']; nlinarith)
        (D.e (ref k)) ht hcs
      refine ⟨hcv.trans (thickening_mono (by linarith : 2 * ρ ≤ 16384 * ρ) _), ?_⟩
      have hh := ((hcover (by norm_num)).2 (ref k)).2
      dsimp only [Function.comp_apply]
      nlinarith [sq_nonneg ρ]
  have hsupport (k : Fin K) : (⋃ i, D'.W i k) = assignedFiber f (fun j => ⋃ i, D.W i j) k := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      obtain ⟨j, hj, hp⟩ := (mem_mergePieces f D.W i k p).mp hi
      exact ⟨j, hj, mem_iUnion.mpr ⟨i, hp⟩⟩
    · rintro ⟨j, hj, hp⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨i, (mem_mergePieces f D.W i k p).mpr ⟨j, hj, hi⟩⟩
  refine ⟨D', hvalid, ?_, ?_⟩
  · intro k p
    change q K {j | D.γ (ref j) = k ∧ p ∈ ⋃ i, D'.W i j} ≤ _
    simp_rw [hsupport]
    exact hcount k p
  · exact mergePieces_total_measure volume f D.W (fun i j => (hW i j).1)
      (fun i j j' hne => (hW i j).2.2 j' hne)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
