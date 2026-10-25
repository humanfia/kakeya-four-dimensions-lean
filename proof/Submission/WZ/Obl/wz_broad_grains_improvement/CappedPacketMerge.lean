-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.CappedPacketMerge.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.PrismCapsTransport
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.FiberPackets
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PacketCrossing
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.RotationCrossing

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_move_two_capped_prism_overlap
  (PrismData fiber_narrow_packets valid_prism_nonempty packet_prism_in_core
   packet_prism_crossing contained_direction_coarse_norm rotated_tube_mem
   rotated_prism_mem rotated_prism_crossing_iff valid_merge_at_scale mem_mergePieces)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (coarseLinear dualLinear rotatedFrame rotatedFrame_apply boxAxis geometricPacketOverlap assignedFiber)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit pd)

set_option maxHeartbeats 1500000 in
/-- Realize one close packet pair in the physical coordinates. All substantial
geometry is supplied by the accepted packet enclosure and crossing lemmas. -/
private theorem close_prism_pair {ω ζ d h ρ c s : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/16384) (hdc : 4*d ≤ c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ ρ*s*c)
    (H : D.Valid ω ζ d h ρ c x v Y 1)
    (hv : ∀ i, ‖v i‖ = 1) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (R : Fin D.N → V ≃ₗᵢ[ℝ] V)
    (hR : ∀ k, |R k (D.w k) 0| ≤ ρ ∧ |R k (D.w k) 1| ≤ ρ)
    (haxes : ∀ j,
      ‖dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)‖ ≤ 25*ρ ∧
      ‖dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 1)‖ ≤ 25*ρ ∧
      ‖coarseLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 2)‖ ≤ 43)
    (j k : Fin D.L) (hγ : D.γ k = D.γ j)
    (hangle : ‖unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)) -
      unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ k)) (D.e k)) 0))‖ ≤ s/100)
    (hcenter : ‖coarseLinear ρ (R (D.γ j) (D.z j-D.z k))‖ ≤ c/100)
    (hshort : |inner ℝ (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ k)) (D.e k)) 0)))
      (coarseLinear ρ (R (D.γ j) (D.z j-D.z k)))| ≤ s*c/100)
    (hclear : ∀ i, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ*c) c (D.z j) (D.e j),
      96*c < dist p (x i) ∧ 96*c < dist p (x i+v i)) :
    P D.a (ρ*c) c (D.z j) (D.e j) ⊆
      P (524288*ρ*s*c) (524288*ρ*c) (32*c) (D.z k) (D.e k) ∧
    ∀ i, (D.W i j).Nonempty →
      (∀ p ∈ T d (x i) (v i) ∩ frontier
          (P (524288*ρ*s*c) (524288*ρ*c) (32*c) (D.z k) (D.e k)),
        |D.e k (p-D.z k) 2| = (32*c)/2) ∧
      ∀ t ∈ ({-(32*c)/2,(32*c)/2} : Set ℝ), ∃ p ∈ T d (x i) (v i) ∩
        P (524288*ρ*s*c) (524288*ρ*c) (32*c) (D.z k) (D.e k),
        D.e k (p-D.z k) 2 = t := by
  have ha : 0 < D.a := hd.trans_le H.1
  have hc : 0 < c := ha.trans_le (H.2.1.trans H.2.2.1)
  have hρ1 : ρ ≤ 1 := by linarith
  have hkaxes := haxes k
  rw [hγ] at hkaxes hangle hshort
  have hangle' := hangle.trans (show s/100 ≤ s by linarith)
  let Rj := R (D.γ j)
  constructor
  · intro p hp
    have hcore := packet_prism_in_core (ρ := ρ) (a := D.a) (c := c) (s := s)
      (z := Rj (D.z j)) (z₀ := Rj (D.z k))
      (rotatedFrame Rj (D.e j)) (rotatedFrame Rj (D.e k))
      hρ hρ1 ha H.2.1 hc hs has hkaxes.1 hkaxes.2.1 (haxes j).2.2 hangle'
      (by simpa only [← map_sub] using hcenter)
      (by simpa only [← map_sub] using hshort)
      ((rotated_prism_mem Rj (D.e j) D.a (ρ*c) c (D.z j) p).mpr hp)
    have hcore' := (rotated_prism_mem Rj (D.e k)
      ((524288*ρ*s*c)/8) ((524288*ρ*c)/8) ((32*c)/8) (D.z k) p).mp hcore
    exact ⟨hcore'.1.trans (by nlinarith [mul_pos (mul_pos hρ hs) hc]),
      hcore'.2.1.trans (by nlinarith [mul_pos hρ hc]), hcore'.2.2.trans (by linarith)⟩
  · intro i hi
    obtain ⟨p, hp⟩ := hi
    have hpU := ((H.2.2.2.2.1 i j).2.1 hp).2
    have hpT := hYT i ((H.2.2.2.2.1 i j).2.1 hp).1
    obtain ⟨ht, hfr, hend⟩ := H.2.2.2.2.2.2.2.1 i j ⟨p,hp⟩
    rw [(H.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)).1] at ht
    have hrotT : T d (Rj (x i)) (Rj (v i)) ⊆
        T ρ (Rj (D.y (D.γ j))) (Rj (D.w (D.γ j))) := by
      intro q hq
      have hq' : Rj (Rj.symm q) ∈ T d (Rj (x i)) (Rj (v i)) := by simpa using hq
      have hqold := (rotated_tube_mem Rj d (x i) (v i) _).mp hq'
      have hqnew := (rotated_tube_mem Rj ρ (D.y (D.γ j)) (D.w (D.γ j)) _).mpr (ht hqold)
      simpa only [Rj.apply_symm_apply] using hqnew
    have hvrot : ‖Rj (v i)‖ = 1 := by simpa using hv i
    have hwrot : ‖Rj (D.w (D.γ j))‖ = 1 := by
      simpa using H.2.2.2.2.2.2.2.2.2.2.1 (D.γ j)
    have hvcoarse := contained_direction_coarse_norm hd hρ hvrot hwrot
      (hR (D.γ j)).1 (hR (D.γ j)).2 hrotT
    have hcrossrot := (rotated_prism_crossing_iff Rj (D.e j) d D.a (ρ*c) c
      (x i) (v i) (D.z j)).mpr ⟨hfr,hend⟩
    have hclr := hclear i ⟨p,hp⟩ p hpU
    apply (rotated_prism_crossing_iff Rj (D.e k) d (524288*ρ*s*c) (524288*ρ*c)
      (32*c) (x i) (v i) (D.z k)).mp
    apply packet_prism_crossing (rotatedFrame Rj (D.e j)) (rotatedFrame Rj (D.e k))
      hd H.1 hdc hρ hρsmall H.2.1 hs hs1 has hvrot hvcoarse
      hkaxes.1 hkaxes.2.1 (haxes j).2.2 hangle'
      (by simpa only [← map_sub] using hcenter)
      (by simpa only [← map_sub] using hshort) hcrossrot.2
      ⟨(rotated_tube_mem Rj d (x i) (v i) p).mpr hpT,
        (rotated_prism_mem Rj (D.e j) D.a (ρ*c) c (D.z j) p).mpr hpU⟩
    · simpa only [Rj.dist_map] using hclr.1
    · simpa only [← map_add, Rj.dist_map] using hclr.2

set_option maxHeartbeats 1500000 in
/-- Merge the accepted narrow packets while retaining their normalized caps.
This strengthens the overlap construction by retaining its actual column map. -/
theorem capped_narrow_prism_merge {ω ζ d h h' ρ c s : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hhh : h ≤ h') (hh : 0 ≤ h)
    (hβ : 0 ≤ ω*ζ/100) (hρsmall : ρ ≤ 1/16384) (hcsmall : c ≤ 1/1048576)
    (hdc : 4*d ≤ c) (hs : 0 < s) (hs1 : s ≤ 1) (has : D.a ≤ ρ*s*c)
    (hbudget : 8796093022208*d^h'*ρ*s*c ≤ d^h*D.a)
    (hangular : d^(-h)*(16384:ℝ)^(ω*ζ/100) ≤ d^(-h'))
    (hv : ∀ i, ‖v i‖ = 1) (hYI : ∀ i, Y i ⊆ I) (hYT : ∀ i, Y i ⊆ T d (x i) (v i))
    (H : D.Valid ω ζ d h ρ c x v Y 1) (Hcaps : D.HasCaps d h ρ c)
    (hX : X (16384*ρ) D.N D.y D.w)
    (R : Fin D.N → V ≃ₗᵢ[ℝ] V)
    (hR : ∀ k, |R k (D.w k) 0| ≤ ρ ∧ |R k (D.w k) 1| ≤ ρ)
    (hclear : ∀ i j, (D.W i j).Nonempty → ∀ p ∈ P D.a (ρ*c) c (D.z j) (D.e j),
      96*c < dist p (x i) ∧ 96*c < dist p (x i+v i))
    (hnarrow : ∀ j j' p, D.γ j = D.γ j' → p ∈ ⋃ i, D.W i j → p ∈ ⋃ i, D.W i j' →
      s = 1 ∨ pd (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j)) (D.e j)) 0)))
        (unit (dualLinear ρ (boxAxis (rotatedFrame (R (D.γ j')) (D.e j')) 0))) ≤ s) :
    ∃ D' : PrismData n, D'.Valid ω ζ d h' (16384*ρ) (32*c) x v Y 1 ∧
      D'.HasCaps d h' (16384*ρ) (32*c) ∧
      ∀ k p, q D'.L {j | D'.γ j = k ∧ p ∈ ⋃ i, D'.W i j} ≤ geometricPacketOverlap := by
  classical
  have ha : 0 < D.a := hd.trans_le H.1
  have hc : 0 < c := ha.trans_le (H.2.1.trans H.2.2.1)
  have hρ : 0 < ρ := (mul_pos_iff.mp (ha.trans_le H.2.1)).resolve_right
    (by rintro ⟨_, hn⟩; linarith) |>.1
  have hρ1 : ρ ≤ 1 := by linarith
  have hW := H.2.2.2.2.1
  have hw := H.2.2.2.2.2.2.2.2.2.2.1
  have hcover := H.2.2.2.2.2.2.2.2.2.2.2.1 (by decide)
  have hsource (j : Fin D.L) : (⋃ i, D.W i j).Nonempty ∧
      (⋃ i, D.W i j) ⊆ P D.a (ρ*c) c (D.z j) (D.e j) ∧ (⋃ i, D.W i j) ⊆ I := by
    obtain ⟨i, hi⟩ := valid_prism_nonempty D hd H j
    exact ⟨hi.mono (subset_iUnion (fun i => D.W i j) i),
      iUnion_subset fun i => (hW i j).2.1.trans inter_subset_right,
      iUnion_subset fun i => (hW i j).2.1.trans (inter_subset_left.trans (hYI i))⟩
  have haxes (j : Fin D.L) :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_coarse_axis_bounds hρ hρ1 hρ.le le_rfl
      (rotatedFrame (R (D.γ j)) (D.e j)) (R (D.γ j) (D.w (D.γ j)))
      (by simpa only [LinearIsometryEquiv.norm_map] using hw (D.γ j))
      (hR (D.γ j)).1 (hR (D.γ j)).2
      (by simpa only [rotatedFrame_apply] using (hcover.2 j).2)
  obtain ⟨K, f, ref, href, hγ, hclose, hcount⟩ := fiber_narrow_packets hρ hρ1 ha H.2.1 hc
    H.2.2.2.1 hs hs1 has D.z D.e (fun j => ⋃ i, D.W i j) D.γ R hsource
    (fun j => (haxes j).2.2) hnarrow
  have hgeom (j : Fin D.L) := close_prism_pair D hd hρ hρsmall hdc hs hs1 has H hv hYT R hR
    haxes j (ref (f j)) (hγ j) (hclose j (ref (f j)) (href (f j)).symm).2.1
    (hclose j (ref (f j)) (href (f j)).symm).2.2.1
    (hclose j (ref (f j)) (href (f j)).symm).2.2.2 (fun i => hclear i j)
  let a' := 524288*ρ*s*c
  let c' := 32*c
  have ha' : d ≤ a' := by dsimp [a']; nlinarith [H.1]
  have hab' : a' ≤ (16384*ρ)*c' := by dsimp [a',c']; nlinarith [mul_pos hρ hc]
  have hbc' : (16384*ρ)*c' ≤ c' := by dsimp [c']; nlinarith
  have hc' : c' ≤ 1 := by dsimp [c']; linarith
  have hmiddle : (16384*ρ)*c' = 524288*ρ*c := by dsimp [c']; ring
  have hvol (k : Fin K) (j : Fin D.L) :
      O (d^h') * volume (P a' ((16384*ρ)*c') c' (D.z (ref k)) (D.e (ref k))) ≤
      O (d^h) * volume (P D.a (ρ*c) c (D.z j) (D.e j)) := by
    rw [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume
        (hd.trans_le ha').le (by dsimp [c']; positivity) (by dsimp [c']; positivity),
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozen_prism_volume ha.le
        (mul_pos hρ hc).le hc.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h'),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.le h)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (8796093022208*d^h'*ρ*s*c)*(ρ*c^2) := by dsimp [a',c']; ring
      _ ≤ (d^h*D.a)*(ρ*c^2) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = _ := by ring
  let D' := D.mergeScale (16384*ρ) f a' (D.z ∘ ref) (D.e ∘ ref) (D.γ ∘ ref)
  have H' : D'.Valid ω ζ d h' (16384*ρ) c' x v Y 1 := by
    apply valid_merge_at_scale D x v Y hd hd1 hhh hh hβ (by linarith : ρ ≤ 16384*ρ)
      (by simpa only [mul_div_cancel_right₀ _ hρ.ne'] using hangular) hX H
      f (D.z ∘ ref) (D.e ∘ ref) (D.γ ∘ ref) hγ ha' hab' hbc' hc'
    · intro j
      simpa only [hmiddle,Function.comp_apply] using (hgeom j).1
    · intro k
      exact ⟨ref k,href k,hvol k (ref k)⟩
    · intro i j hi
      simpa only [hmiddle,Function.comp_apply] using (hgeom j).2 i hi
    · intro k
      obtain ⟨i, hi⟩ := valid_prism_nonempty D hd H (ref k)
      have hcross := ((hgeom (ref k)).2 i hi).2
      rw [href k] at hcross
      have ht := (H.2.2.2.2.2.2.2.1 i (ref k) hi).1
      rw [hcover.1] at ht
      have hlarge := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_subset_expanded_coarse
        (hd.trans_le ha').le (by simpa only [hmiddle] using hab')
        (by positivity : 0 < 524288*ρ*c) (by positivity : 0 < 32*c)
        (by nlinarith : 2*(524288*ρ*c) ≤ ρ) (D.e (ref k)) ht hcross
      constructor
      · rw [hmiddle]
        change P a' (524288*ρ*c) (32*c) (D.z (ref k)) (D.e (ref k)) ⊆
          T (16384*ρ) (D.y (D.γ (ref k))) (D.w (D.γ (ref k)))
        exact hlarge.trans (thickening_mono (by linarith : 2*ρ ≤ 16384*ρ) _)
      · change (D.e (ref k) (D.w (D.γ (ref k)))) 0 ^ 2 +
          (D.e (ref k) (D.w (D.γ (ref k)))) 1 ^ 2 ≤ _
        have hh' := (hcover.2 (ref k)).2
        nlinarith [sq_nonneg ρ]
  have Hcap' : D'.HasCaps d h' (16384*ρ) c' := caps_of_prism_merge D hd f
    (fun k => ⟨ref k,href k⟩) (D.z ∘ ref) (D.e ∘ ref) (D.γ ∘ ref)
    (fun i j => (hW i j).1) (fun i j j' hne => (hW i j).2.2 j' hne) Hcaps
    (fun k j _ => hvol k j)
  refine ⟨D',H',Hcap',?_⟩
  intro k p
  have hsupport (l : Fin K) : (⋃ i, D'.W i l) = assignedFiber f (fun j => ⋃ i, D.W i j) l := by
    ext p
    simp only [mem_iUnion, assignedFiber, mem_ofPred_eq]
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨j,hj,hp⟩ := (mem_mergePieces f D.W i l p).mp hi
      exact ⟨j,hj,i,hp⟩
    · rintro ⟨j,hj,i,hi⟩
      exact ⟨i,(mem_mergePieces f D.W i l p).mpr ⟨j,hj,hi⟩⟩
  change q K {l | D.γ (ref l) = k ∧ p ∈ ⋃ i,D'.W i l} ≤ _
  simp_rw [hsupport]
  exact hcount k p

end WangZahlLot.Obl.wz_broad_grains_improvement
