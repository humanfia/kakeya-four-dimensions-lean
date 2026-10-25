-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GeometricPackets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AngularPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SpatialPackets
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd)

local instance geometricPacketsDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def geometricPacketOverlap : ℕ := (2 * 2003 ^ 3) ^ 2 * 50003 ^ 3

lemma active_packet_count {n N : ℕ} (f : Fin n → Fin N) (Y : Fin n → Set V) (p : V) :
    bodyCount (assignedFiber f Y) p =
      (((Finset.univ.filter fun i => p ∈ Y i).image f).card : ℝ) := by
  have he : {k | p ∈ assignedFiber f Y k} =
      (↑((Finset.univ.filter fun i => p ∈ Y i).image f) : Set (Fin N)) := by
    ext k
    constructor
    · rintro ⟨i, hi, hp⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, hi⟩
    · intro hk
      obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hk
      exact ⟨i, hfi, (Finset.mem_filter.mp hi).2⟩
  change ({k | p ∈ assignedFiber f Y k}.ncard : ℝ) = _
  rw [he, Set.ncard_coe_finset]

/-- Once all incidences are angularly narrow, grains have packets with a
uniform overlap bound, close normalized centers and normals, and close
original long directions. -/
theorem narrow_geometric_packets {n : ℕ} {s c : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 < c)
    (u : Fin n → OrthonormalBasis (Fin 3) ℝ V) (z l : Fin n → V)
    (Y : Fin n → Set V) (F : V → V) (hl : ∀ i, ‖l i‖ = 1)
    (hsource : ∀ i p, p ∈ Y i →
      ‖F p - z i‖ ≤ 25 * c ∧ |inner ℝ (u i 0) (F p - z i)| ≤ s * c)
    (hnarrow : ∀ i j p, p ∈ Y i → p ∈ Y j → s = 1 ∨ pd (u i 0) (u j 0) ≤ s) :
    ∃ L : ℕ, ∃ f : Fin n → Fin L, ∃ ref : Fin L → Fin n,
      (∀ k, f (ref k) = k) ∧
      (∀ i j, f i = f j →
        ‖u i 0 - u j 0‖ ≤ s / 100 ∧ ‖l i - l j‖ ≤ 1 / 50 ∧
        ‖z i - z j‖ ≤ c / 100 ∧ |inner ℝ (u j 0) (z i - z j)| ≤ s * c / 100) ∧
      (∀ p, bodyCount (assignedFiber f Y) p ≤ geometricPacketOverlap) := by
  obtain ⟨N, g, refg, hrefg, hcloseg, hcountg, hunitg⟩ := angular_grid_partition hs (fun i => u i 0)
  obtain ⟨M, d, refd, hrefd, hclosed, hcountd, hunitd⟩ :=
    angular_grid_partition (by norm_num : (0 : ℝ) < 2) l
  have hMall : M ≤ 2 * 2003 ^ 3 := by
    have hh := hcountd Finset.univ (fun i _ j _ => by
      apply (min_le_left _ _).trans
      calc
        ‖l i - l j‖ ≤ ‖l i‖ + ‖l j‖ := norm_sub_le _ _
        _ = 2 := by rw [hl i, hl j]; norm_num)
    have he : Finset.univ.image d = Finset.univ := by
      ext k
      simp only [Finset.mem_univ, iff_true]
      exact Finset.mem_image.mpr ⟨refd k, Finset.mem_univ _, hrefd k⟩
    simpa only [he, Finset.card_univ, Fintype.card_fin] using hh
  have hframe (i : Fin n) : ‖u (refg (g i)) 0 - u i 0‖ ≤ s / 100 :=
    hcloseg _ _ (hrefg _)
  have hactive (p : V) : ((Finset.univ.filter fun i => p ∈ Y i).image g).card ≤ 2 * 2003 ^ 3 := by
    by_cases hsone : s = 1
    · exact (hunitg _ (fun i _ => by rw [(u i).norm_eq_one, hsone])).trans (by norm_num)
    · apply hcountg
      intro i hi j hj
      exact (hnarrow i j p (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2).resolve_left hsone
  obtain ⟨L, f, ref, href, hclose, hcount⟩ := spatial_grid_partition hs hs1 hc g d
    (fun k => u (refg k)) (fun i => u i 0) z Y F hframe hsource hactive
  refine ⟨L, f, ref, href, ?_, ?_⟩
  · intro i j hij
    obtain ⟨hg, hd, hz, hshort⟩ := hclose i j hij
    exact ⟨hcloseg i j hg, by
      have hh := hclosed i j hd
      norm_num at hh ⊢
      exact hh, hz, hshort⟩
  · intro p
    rw [active_packet_count]
    apply Nat.cast_le.mpr
    have hh := (hcount p).trans (Nat.mul_le_mul_left ((2 * 2003 ^ 3) * 50003 ^ 3) hMall)
    convert hh using 1
    dsimp [geometricPacketOverlap]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
